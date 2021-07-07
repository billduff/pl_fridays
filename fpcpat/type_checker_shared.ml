open! Core
open Abt

(* CR-soon wduff: Think about error messages in Abt_to_ast as well as both type checkers. Ideally,
   include locations. *)

let rec eval_type_aliases exp =
  match Exp.out exp with
  | Var _ -> exp
  | Fun (arg_pat, body) -> Exp.fun_ (arg_pat, eval_type_aliases body)
  | Ap (func, arg) -> Exp.ap (eval_type_aliases func, eval_type_aliases arg)
  | Record fields ->
    Exp.record (List.map fields ~f:(fun (label, exp) -> (label, eval_type_aliases exp)))
  | Inj (label, exp) -> Exp.inj (label, eval_type_aliases exp)
  | Fold exp -> Exp.fold (eval_type_aliases exp)
  | Match (exp, cases) ->
    Exp.match_
      (eval_type_aliases exp,
       List.map cases ~f:(fun (pat, exp) ->
         (pat, eval_type_aliases exp)))
  | Fix (var, body) ->
    Exp.fix (var, eval_type_aliases body)
  | Let ((pat, exp1), exp2) ->
    Exp.let_ ((pat, eval_type_aliases exp1), eval_type_aliases exp2)
  | Let_type ((typ_var, typ), exp) -> Exp.subst Typ typ typ_var exp
  | Ascribe (exp, typ) -> Exp.ascribe (eval_type_aliases exp, typ)
;;

module Pat_constraint = struct
  module Simple = struct
    type t =
      | True
      | Record of (string * t) list
      | Inj of string * t
      | Fold of t
    [@@deriving sexp_of]
  end

  type t =
    | True
    | False
    | Or_records of t String.Map.t list
    | Or_injs of t String.Map.t
    | Fold of t
  [@@deriving sexp_of]

  let rec cartesian_product = function
    | [] -> [[]]
    | l :: ls ->
      let rest = cartesian_product ls in
      List.concat_map l ~f:(fun x ->
        List.map rest ~f:(fun l' -> x :: l'))
  ;;

  let rec make (ts : Simple.t list) =
    match ts with
    | [] -> False
    | True :: _ -> True
    | Record _ :: _ ->
      List.filter_map ts ~f:(function
        | True -> None
        | Record fields -> Some fields
        | _ -> assert false)
      |> cartesian_product
      |> List.map ~f:(fun fields ->
        String.Map.of_alist_multi fields
        |> Map.map ~f:make)
      |> Or_records
    | Inj _ :: _ ->
      List.filter_map ts ~f:(function
        | True -> None
        | Inj (label, t) -> Some (label, t)
        | _ -> assert false)
      |> String.Map.of_alist_multi
      |> Map.map ~f:make
      |> Or_injs
    | Fold _ :: _ ->
      List.filter_map ts ~f:(function
        | True -> None
        | Fold t -> Some t
        | _ -> assert false)
      |> make
      |> Fold
  ;;

  let rec singleton (t : Simple.t) =
    match t with
    | True -> True
    | Record fields ->
      List.map fields ~f:(fun (label, t) ->
        String.Map.singleton label (singleton t))
      |> Or_records
    | Inj (label, t) -> Or_injs (String.Map.singleton label (singleton t))
    | Fold t -> Fold (singleton t)
  ;;

  (* Note: Similar to our choice with subtyping above, we don't check for empty types (for which
     [False] is arguably exhaustive). *)
  let rec is_exhaustive t ~wrt:typ =
    match t with
    | True -> true
    | False -> false
    | Or_records records ->
      (match Typ.out typ with
       | Prod fields ->
         let fields = String.Map.of_alist_exn fields in
         List.for_all records ~f:(fun ts_by_fields ->
           List.exists (Map.to_alist ts_by_fields) ~f:(fun (label, t) ->
             is_exhaustive t ~wrt:(Map.find_exn fields label)))
       | _ -> failwith "type error")
    | Or_injs ts_by_label ->
      (match Typ.out typ with
       | Sum clauses ->
         List.for_all clauses ~f:(fun (label, typ) ->
           match Map.find ts_by_label label with
           | None -> false
           | Some t -> is_exhaustive t ~wrt:typ)
       | _ -> failwith "type error")
    | Fold t ->
      (match Typ.out typ with
       | Rec (typ_var, typ') ->
         is_exhaustive t ~wrt:(Typ.subst Typ typ typ_var typ')
       | _ -> failwith "type error")
  ;;

  let rec check_not_redundant_then_or ~wrt ts (t : Simple.t) =
    match (ts, t) with
    | True, _ -> None
    | False, _ -> Some (make [ t ])
    | _, True -> Option.some_if (is_exhaustive ~wrt ts) True
    | Or_records records, Record fields ->
      let records =
        List.filter_map records ~f:(fun ts_by_field ->
          Map.merge
            ts_by_field
            (String.Map.of_alist_exn fields)
            ~f:(fun ~key:_ -> function
              | `Both (ts, t) -> Some (check_not_redundant_then_or ~wrt ts t)
              | `Left ts -> Some (Option.some_if (is_exhaustive ~wrt ts) True)
              | `Right _ -> Some None)
          |> Map.to_alist
          |> List.map ~f:(fun (label, opt) ->
            Option.map opt ~f:(fun ts -> (label, ts)))
          |> Option.all
          |> Option.map ~f:String.Map.of_alist_exn)
      in
      (match records with
       | [] -> None
       | _::_ -> Some (Or_records records))
    | Or_injs ts_by_label, Inj (label, t) ->
      (match String.Map.find ts_by_label label with
       | None -> Some (Or_injs (String.Map.add_exn ts_by_label ~key:label ~data:(make [ t ])))
       | Some ts ->
         (match check_not_redundant_then_or ~wrt ts t with
          | None -> None
          | Some ts ->
            Some (Or_injs (Map.set ts_by_label ~key:label ~data:ts))))
    | Fold ts, Fold t -> check_not_redundant_then_or ~wrt ts t
    | _ -> assert false
  ;;

  let or_list_check_irredundant ts ~wrt =
    List.fold_until
      ts
      ~init:False
      ~f:(fun acc pat_constr ->
        match check_not_redundant_then_or ~wrt acc pat_constr with
        | None -> Stop None
        | Some pat_constr -> Continue pat_constr)
      ~finish:Option.some
  ;;
end
