open! Core
open Abt

let rec try_pattern (pat : Pat.t) (exp : Exp.t) =
  match (pat, Exp.out exp) with
  | (Wild, _) -> Some []
  | (Var var, _) -> Some [ (exp, var) ]
  | (Record pat_fields, Record exp_fields) ->
    let exp_fields = String.Table.of_alist_exn exp_fields in
    List.map pat_fields ~f:(fun (label, pat) ->
      try_pattern pat (Hashtbl.find_exn exp_fields label))
    |> Option.all
    |> Option.map ~f:List.concat
  | (Inj (pat_label, pat), Inj (exp_label, exp)) ->
    (match String.equal pat_label exp_label with
     | true -> try_pattern pat exp
     | false -> None)
  | (Fold pat, Fold exp) ->
    try_pattern pat exp
  | (Ascribe (pat, _), _) -> try_pattern pat exp
  | _ -> assert false
;;

let apply_subst subst exp =
  (* CR-soon wduff: It's kinda sad that abbot doesn't give us a way to build up a big subst
     directly, because it would probably be less code and more efficient than building up
     this list only to iterate over it asking abbot to build up a substitution inside the
     expression. *)
  List.fold subst ~init:exp ~f:(fun body (value, var) ->
    Exp.subst Exp value var body)
;;

let rec eval exp =
  match Exp.out exp with
  | Var _ -> assert false
  | Fun _ -> exp
  | Ap (func, arg) ->
    (match Exp.out (eval func) with
     | Fun (arg_pat, body) ->
       let arg_val = eval arg in
       let subst = Option.value_exn (try_pattern arg_pat arg_val) in
       eval (apply_subst subst body)
     | _ -> raise_s [%message (exp_to_string exp : string)])
  | Record fields ->
    Exp.record (List.map fields ~f:(fun (label, exp) -> (label, eval exp)))
  | Inj (label, exp) -> Exp.inj (label, eval exp)
  | Fold exp -> Exp.fold (eval exp)
  | Match (exp, cases) ->
    let value = eval exp in
    List.find_map_exn cases ~f:(fun (pat, exp) ->
      Option.map (try_pattern pat value) ~f:(fun subst -> apply_subst subst exp))
    |> eval
  | Fix (var, body) ->
    (* This will infinite loop unless exp evaluates to a value without needing to use var. *)
    eval (Exp.subst Exp exp var body)
  | Let ((pat, exp1), exp2) ->
    let subst = Option.value_exn (try_pattern pat exp1) in
    eval (apply_subst subst exp2)
  | Let_type (_, exp) -> eval exp
  | Ascribe (exp, _) -> eval exp
;;
