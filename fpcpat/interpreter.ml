open! Core

module Abt_of_ast : sig
  val convert : Ast.Exp.t -> Abt.Exp.t
end = struct
  let rec convert_typ context : Ast.Typ.t -> Abt.Typ.t = function
    | Var var_name ->
      (match Map.find context var_name with
       | Some var -> Abt.Typ.var var
       | None ->
         raise_s [%message "unbound variable" (var_name : string)])
    | Arrow (typ1, typ2) ->
      Abt.Typ.arrow (convert_typ context typ1, convert_typ context typ2)
    | Prod fields -> Abt.Typ.prod (convert_typ_list context fields)
    | Sum clauses -> Abt.Typ.sum (convert_typ_list context clauses)
    | Rec (var_name, typ) ->
      let var = Abt.Typ.Var.create var_name in
      let context = String.Map.set context ~key:var_name ~data:var in
      Abt.Typ.rec_ (var, convert_typ context typ)

  and convert_typ_list context l =
    match List.contains_dup ~compare:[%compare: string * _] l with
    | true -> failwith "duplicate label"
    | false ->
      List.map l ~f:(fun (label, typ) ->
        (label, convert_typ context typ))
  ;;

  let rec convert_pat typ_context
    : Ast.Pat.t -> Abt.Exp.Var.t String.Map.t * Abt.Pat.t = function
    | Wild -> (String.Map.empty, Wild)
    | Var var_name ->
      let var = Abt.Exp.Var.create var_name in
      let context = String.Map.singleton var_name var in
      (context, Var var)
    | Record fields ->
      (match List.contains_dup ~compare:[%compare: string * _] fields with
       | true -> failwith "duplicate field name"
       | false ->
         let (context, fields) =
           List.fold_map fields ~init:String.Map.empty ~f:(fun acc_context (label, pat) ->
             let (this_context, pat) = convert_pat typ_context pat in
             let context =
               Map.merge_skewed acc_context this_context ~combine:(fun ~key:var_name _var1 _var2 ->
                 (* CR-soon wduff: Location info would be nice. *)
                 raise_s [%message "Duplicate variable name in pattern." (var_name : string)])
             in
             (context, (label, pat)))
         in
         (context, Record fields))
    | Inj (label, pat) ->
      let (context, pat) = convert_pat typ_context pat in
      (context, Inj (label, pat))
    | Fold pat ->
      let (context, pat) = convert_pat typ_context pat in
      (context, Fold pat)
    | Ascribe (pat, typ) ->
      let (context, pat) = convert_pat typ_context pat in
      (context, Ascribe (pat, convert_typ typ_context typ))
  ;;

  let convert_pat_and_extend_context typ_context context pat =
    let (pat_context, pat) = convert_pat typ_context pat in
    let context =
      Map.merge_skewed context pat_context ~combine:(fun ~key:_ _shadowed_var pat_var -> pat_var)
    in
    (context, pat)
  ;;

  let rec convert_exp typ_context context : Ast.Exp.t -> Abt.Exp.t = function
    | Var var_name ->
      (match Map.find context var_name with
       | Some var -> Abt.Exp.var var
       | None ->
         raise_s [%message "unbound variable" (var_name : string)])
    | Fun (pat, exp) ->
      let (context, pat) = convert_pat_and_extend_context typ_context context pat in
      Abt.Exp.fun_ (pat, convert_exp typ_context context exp)
    | Ap (exp1, exp2) ->
      Abt.Exp.ap (convert_exp typ_context context exp1, convert_exp typ_context context exp2)
    | Record fields ->
      (match List.contains_dup ~compare:[%compare: string * _] fields with
       | true -> failwith "duplicate field name"
       | false ->
         Abt.Exp.record
           (List.map fields ~f:(fun (label, exp) ->
              (label, convert_exp typ_context context exp))))
    | Inj (label, exp) -> Abt.Exp.inj (label, convert_exp typ_context context exp)
    | Fold exp -> Abt.Exp.fold (convert_exp typ_context context exp)
    | Match (exp, cases) ->
      Abt.Exp.match_
        (convert_exp typ_context context exp,
         List.map cases ~f:(fun (pat, exp) ->
           let (context, pat) = convert_pat_and_extend_context typ_context context pat in
           (pat, convert_exp typ_context context exp)))
    | Fix (var_name, exp) ->
      let var = Abt.Exp.Var.create var_name in
      let context = String.Map.set context ~key:var_name ~data:var in
      Abt.Exp.fix (var, convert_exp typ_context context exp)
    | Let ((pat, exp1), exp2) ->
      let exp1 = convert_exp typ_context context exp1 in
      let (context, pat) = convert_pat_and_extend_context typ_context context pat in
      let exp2 = convert_exp typ_context context exp2 in
      Abt.Exp.let_ ((pat, exp1), exp2)
    | Let_type ((var_name, typ), exp) ->
      let typ = convert_typ typ_context typ in
      let var = Abt.Typ.Var.create var_name in
      let typ_context = String.Map.set typ_context ~key:var_name ~data:var in
      let exp = convert_exp typ_context context exp in
      Abt.Exp.let_type ((var, typ), exp)
    | Ascribe (exp, typ) ->
      Abt.Exp.ascribe (convert_exp typ_context context exp, convert_typ typ_context typ)
  ;;

  let convert ast =
    convert_exp String.Map.empty String.Map.empty ast
  ;;
end

module Dynamics = struct
  let rec try_pattern (pat : Abt.Pat.t) (exp : Abt.Exp.t) =
    match (pat, Abt.Exp.out exp) with
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
      Abt.Exp.subst Exp value var body)
  ;;

  let rec eval exp =
    match Abt.Exp.out exp with
    | Var _ -> assert false
    | Fun _ -> exp
    | Ap (func, arg) ->
      (match Abt.Exp.out (eval func) with
       | Fun (arg_pat, body) ->
         let arg_val = eval arg in
         let subst = Option.value_exn (try_pattern arg_pat arg_val) in
         eval (apply_subst subst body)
       | _ -> raise_s [%message (Abt.exp_to_string exp : string)])
    | Record fields ->
      Abt.Exp.record (List.map fields ~f:(fun (label, exp) -> (label, eval exp)))
    | Inj (label, exp) -> Abt.Exp.inj (label, eval exp)
    | Fold exp -> Abt.Exp.fold (eval exp)
    | Match (exp, cases) ->
      let value = eval exp in
      List.find_map_exn cases ~f:(fun (pat, exp) ->
        Option.map (try_pattern pat value) ~f:(fun subst -> apply_subst subst exp))
      |> eval
    | Fix (var, body) ->
      (* This will infinite loop unless exp evaluates to a value without needing to use var. *)
      eval (Abt.Exp.subst Exp exp var body)
    | Let ((pat, exp1), exp2) ->
      let subst = Option.value_exn (try_pattern pat exp1) in
      eval (apply_subst subst exp2)
    | Let_type (_, exp) -> eval exp
    | Ascribe (exp, _) -> eval exp
end

let rec eval_type_aliases exp =
  match Abt.Exp.out exp with
  | Var _ -> exp
  | Fun (arg_pat, body) -> Abt.Exp.fun_ (arg_pat, eval_type_aliases body)
  | Ap (func, arg) -> Abt.Exp.ap (eval_type_aliases func, eval_type_aliases arg)
  | Record fields ->
    Abt.Exp.record (List.map fields ~f:(fun (label, exp) -> (label, eval_type_aliases exp)))
  | Inj (label, exp) -> Abt.Exp.inj (label, eval_type_aliases exp)
  | Fold exp -> Abt.Exp.fold (eval_type_aliases exp)
  | Match (exp, cases) ->
    Abt.Exp.match_
      (eval_type_aliases exp,
       List.map cases ~f:(fun (pat, exp) ->
         (pat, eval_type_aliases exp)))
  | Fix (var, body) ->
    Abt.Exp.fix (var, eval_type_aliases body)
  | Let ((pat, exp1), exp2) ->
    Abt.Exp.let_ ((pat, eval_type_aliases exp1), eval_type_aliases exp2)
  | Let_type ((typ_var, typ), exp) -> Abt.Exp.subst Typ typ typ_var exp
  | Ascribe (exp, typ) -> Abt.Exp.ascribe (eval_type_aliases exp, typ)
;;

module Pat_constraint : sig
  module Simple : sig
    type t =
      | True
      | Record of (string * t) list
      | Inj of string * t
      | Fold of t
  end

  type t

  val singleton : Simple.t -> t
  val or_list_check_irredundant : Simple.t list -> wrt:Abt.Typ.t -> t option

  val is_exhaustive : t -> wrt:Abt.Typ.t -> bool
end = struct
  module Simple = struct
    type t =
      | True
      | Record of (string * t) list
      | Inj of string * t
      | Fold of t
  end

  type t =
    | True
    | False
    | Or_records of t String.Map.t list
    | Or_injs of t String.Map.t
    | Fold of t

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
      let map =
        String.Map.of_alist_exn fields
        |> Map.map ~f:singleton
      in
      Or_records [ map ]
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
      (match Abt.Typ.out typ with
       | Prod fields ->
         let fields = String.Map.of_alist_exn fields in
         List.for_all records ~f:(fun ts_by_fields ->
           List.exists (Map.to_alist ts_by_fields) ~f:(fun (label, t) ->
             is_exhaustive t ~wrt:(Map.find_exn fields label)))
       | _ -> failwith "type error")
    | Or_injs ts_by_label ->
      (match Abt.Typ.out typ with
       | Sum clauses ->
         List.for_all clauses ~f:(fun (label, typ) ->
           match Map.find ts_by_label label with
           | None -> false
           | Some t -> is_exhaustive t ~wrt:typ)
       | _ -> failwith "type error")
    | Fold t ->
      (match Abt.Typ.out typ with
       | Rec (typ_var, typ') ->
         is_exhaustive t ~wrt:(Abt.Typ.subst Typ typ typ_var typ')
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

(* CR-soon wduff: Think about error messages. *)
module Bidirectional_type_checker : sig
  val run_exn : Abt.Exp.t -> Abt.Typ.t
end = struct
  (* This is good to have for completeness, but it doesn't actually have to do anything because we
     already check that types are well-formed in the ast->abt pass. Also this really is "check" not
     "synth", because we need these types to have kind "type", since they come from annotations. *)
  let check_typ (_ : Abt.Typ.t) = ()

  (* CR-soon wduff: This subtyping relation is incomplete in a couple ways:
     1) The way we deal with recursive types is not fully general.
     2) We could consider whether types are inhabited (by values), and take advantage of the
     fact that empty types can be considered subtypes of any other type and functions out of the
     empty type can be considered supertypes of any other type.

     I haven't done (1) because it's really grotty to implement, espcially if you try to implement
     it efficiently.

     I haven't done (2) because  I'm dubious whether relying on type inhabitedness is a good idea,
     since it is often undecidable (e.g. for system F). *)
  let rec subtype typ typ' =
    match (Abt.Typ.out typ, Abt.Typ.out typ') with
    | (Var var, Var var') ->
      (match Abt.Typ.Var.equal var var' with
       | true -> ()
       | false -> failwith "type error")
    | (Arrow (typ1, typ2), Arrow (typ1', typ2')) ->
      subtype typ1' typ1;
      subtype typ2 typ2';
    | (Prod fields, Prod fields') ->
      let fields_map = String.Table.of_alist_exn fields in
      List.iter fields' ~f:(fun (label, typ') ->
        match Hashtbl.find fields_map label with
        | Some typ -> subtype typ typ'
        | None -> failwith "type error")
    | (Sum fields, Sum fields') ->
      let fields_map' = String.Table.of_alist_exn fields' in
      List.iter fields ~f:(fun (label, typ) ->
        match Hashtbl.find fields_map' label with
        | Some typ' -> subtype typ typ'
        | None -> failwith "type error")
    | (Rec (var, typ), Rec (var', typ')) ->
      subtype typ (Abt.Typ.subst Typ (Abt.Typ.var var) var' typ')
    | _ -> failwith "type error"
  ;;

  let rec synth_pat (pat : Abt.Pat.t)
    : Abt.Typ.t Abt.Exp.Var.Map.t * Abt.Typ.t * Pat_constraint.Simple.t =
    match pat with
    | Record fields ->
      let (context, field_typs_and_constrs) =
        List.fold_map fields ~init:Abt.Exp.Var.Map.empty ~f:(fun acc_context (label, pat) ->
          let (this_context, typ, constr) = synth_pat pat in
          let context =
            Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false)
          in
          (context, ((label, typ), (label, constr))))
      in
      let (field_typs, field_constrs) = List.unzip field_typs_and_constrs in
      (context, Abt.Typ.prod field_typs, Record field_constrs)
    | Inj (label, pat) ->
      let (context, typ, constr) = synth_pat pat in
      (context, Abt.Typ.sum [ (label, typ) ], Inj (label, constr))
    | Ascribe (pat, typ) ->
      check_typ typ;
      let (context, constr) = check_pat pat typ in
      (context, typ, constr)
    | Wild | Var _ | Fold _ -> failwithf "could not infer type of %s" (Abt.pat_to_string pat) ()

  and check_pat (pat : Abt.Pat.t) typ =
    match pat with
    | Wild -> (Abt.Exp.Var.Map.empty, True)
    | Var var -> (Abt.Exp.Var.Map.singleton var typ, True)
    | Record fields ->
      (match Abt.Typ.out typ with
       | Prod field_typs ->
         let field_typs = String.Table.of_alist_exn field_typs in
         let (context, field_constrs) =
           (* Note: We deliberately allow fields that show up in the type to be missing from the
              pattern. This is important for subsumption. E.g., if we have a variable bound with
              some record type, and we're matching on that variable, we need the program to continue
              to type check if an expression with a smaller principle type is substituted for the
              variable. *)
           List.fold_map fields ~init:Abt.Exp.Var.Map.empty ~f:(fun acc_context (label, pat) ->
             match Hashtbl.find field_typs label with
             | Some typ ->
               let (this_context, constr) = check_pat pat typ in
               let context =
                 Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false)
               in
               (context, (label, constr))
             | None -> failwith "type error")
         in
         (context, Record field_constrs)
       | _ -> failwith "type error")
    | Inj (label, pat) ->
      (match Abt.Typ.out typ with
       | Sum clause_typs ->
         (match
            List.find_map clause_typs ~f:(fun (label', typ) ->
              match String.equal label label' with
              | true -> Some typ
              | false -> None)
          with
          | Some typ ->
            let (context, constr) = check_pat pat typ in
            (context, Inj (label, constr))
          | None ->
            (* For the same reasoning as missing record fields above, we need to be okay with
               injections that don't appear in the type. We still need to synthesize a type for the
               subpattern, in order to compute the constraint. This might appear to break
               substitution, because again, we now have less type information than before, and may
               therefore not be able to type check. However, that only breaks substitution for
               algorithmic type checking. We can still appeal to the declarative typing rules
               instead (or build a fancier evaluator that carefully carries along the required type
               annotations). *)
            let (context, _, constr) = synth_pat pat in
            (context, Inj (label, constr)))
       | _ -> failwith "type error")
    | Fold pat ->
      (match Abt.Typ.out typ with
       | Rec (typ_var, typ') ->
         let (context, constr) = check_pat pat (Abt.Typ.subst Typ typ typ_var typ') in
         (context, Fold constr)
       | _ -> failwith "type error")
    | Ascribe _ ->
      let (context, typ', constr) = synth_pat pat in
      subtype typ typ';
      (context, constr)
  ;;

  let synth_pat_and_extend_context context pat =
    let (pat_context, typ, constr) = synth_pat pat in
    let context =
      Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
    in
    (context, typ, constr)
  ;;

  let check_pat_and_extend_context context pat typ =
    let (pat_context, constr) = check_pat pat typ in
    let context =
      Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
    in
    (context, constr)
  ;;

  let check_pat_exhaustive pat_constr ~wrt =
    match Pat_constraint.is_exhaustive pat_constr ~wrt with
    | true -> ()
    | false -> failwith "type error"
  ;;

  let rec synth_exp context exp =
    match Abt.Exp.out exp with
    | Var var ->
      (try Map.find_exn context var
       with exn -> raise_s [%message "hrm" (exn : exn) (context : Abt.Typ.t Abt.Exp.Var.Map.t)])
    | Fun (arg_pat, body) ->
      let (context, arg_typ, pat_constr) = synth_pat_and_extend_context context arg_pat in
      check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:arg_typ;
      Abt.Typ.arrow (arg_typ, synth_exp context body)
    | Ap (func, arg) ->
      (match Abt.Typ.out (synth_exp context func) with
       | Arrow (arg_typ, result_typ) ->
         check_exp context arg arg_typ;
         result_typ
       | _ -> failwith "type error")
    | Record fields ->
      List.map fields ~f:(fun (label, exp) ->
        (label, synth_exp context exp))
      |> Abt.Typ.prod
    | Inj (label, exp) ->
      let typ = synth_exp context exp in
      Abt.Typ.sum [ (label, typ) ]
    | Let ((pat, exp1), exp2) ->
      (* This non-determinism is sad, but hopefully most patterns are small, so this won't be too
         expensive. *)
      (match synth_pat_and_extend_context context pat with
       | (context', typ, pat_constr) ->
         check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:typ;
         check_exp context exp1 typ;
         synth_exp context' exp2
       | exception _ ->
         let typ1 = synth_exp context exp1 in
         let (context, pat_constr) = check_pat_and_extend_context context pat typ1 in
         check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:typ1;
         synth_exp context exp2)
    | Ascribe (exp, typ) ->
      check_typ typ;
      check_exp context exp typ;
      typ
    | Fold _ | Match _ | Fix _ -> failwithf "could not infer type of %s" (Abt.exp_to_string exp) ()
    | Let_type _ -> assert false

  and check_exp context exp typ =
    (* CR-soon wduff: We could allow "wildcard" types, and deal with them by switching from checking
       back to synthesizing when checking against a wildcard. This would allow users to, e.g., only
       specify the argument type of a function, though they can do that with patter ascriptions as
       well. *)
    match Abt.Exp.out exp with
    | Fun (arg_pat, body) ->
      (match Abt.Typ.out typ with
       | Arrow (typ1, typ2) ->
         let (context, pat_constr) = check_pat_and_extend_context context arg_pat typ1 in
         check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:typ1;
         check_exp context body typ2
       | _ -> failwith "type error")
    | Record fields ->
      (match Abt.Typ.out typ with
       | Prod field_typs ->
         let fields = String.Map.of_alist_exn fields in
         let field_typs = String.Map.of_alist_exn field_typs in
         ignore
           (Map.merge fields field_typs ~f:(fun ~key:_ -> function
              | `Both (exp, typ) ->
                check_exp context exp typ;
                None
              | `Left exp ->
                (* This code may execute, since it's a call-by-value language, so we have to make
                   sure it's well typed. We don't have a type to check it against, so we have to
                   synthesize one. *)
                ignore (synth_exp context exp : Abt.Typ.t);
                None
              | `Right _ -> failwith "type error")
            : Nothing.t String.Map.t)
       | _ -> failwith "type error")
    | Inj (label, exp) ->
      (match Abt.Typ.out typ with
       | Sum clause_typs ->
         (match
            List.find_map clause_typs ~f:(fun (label', typ) ->
              match String.equal label label' with
              | true -> Some typ
              | false -> None)
          with
          | Some typ -> check_exp context exp typ
          | None -> failwith "type error")
       | _ -> failwith "type error")
    | Fold exp ->
      (match Abt.Typ.out typ with
       | Rec (typ_var, typ') ->
         check_exp context exp (Abt.Typ.subst Typ typ typ_var typ')
       | _ -> failwith "type error")
    | Match (exp, cases) ->
      let typ' = synth_exp context exp in
      let pat_constrs =
        List.map cases ~f:(fun (pat, exp) ->
          let (context, pat_constr) = check_pat_and_extend_context context pat typ' in
          check_exp context exp typ;
          pat_constr)
      in
      (match Pat_constraint.or_list_check_irredundant pat_constrs ~wrt:typ' with
       | None -> failwith "redundant pattern"
       | Some pat_constr -> check_pat_exhaustive pat_constr ~wrt:typ')
    | Fix (var, body) ->
      check_exp (Map.set context ~key:var ~data:typ) body typ
    | Let ((pat, exp1), exp2) ->
      (match synth_pat_and_extend_context context pat with
       | (context', typ', pat_constr) ->
         check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:typ';
         check_exp context exp1 typ';
         check_exp context' exp2 typ
       | exception _ ->
         let typ1 = synth_exp context exp1 in
         let (context, pat_constr) = check_pat_and_extend_context context pat typ1 in
         check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:typ1;
         check_exp context exp2 typ)
    | Var _ | Ap _ | Ascribe _ ->
      let typ' = synth_exp context exp in
      subtype typ' typ
    | Let_type _ -> assert false
  ;;

  let run_exn exp =
    let exp = eval_type_aliases exp in
    synth_exp Abt.Exp.Var.Map.empty exp
  ;;
end

module Hindley_milner_type_checker : sig
  val run_exn : Abt.Exp.t -> Abt.Typ.t
end = struct
  let check_typ (_ : Abt.Typ.t) = ()

  let apply_subst subst typ =
    List.fold subst ~init:typ ~f:(fun acc (typ, var) -> Abt.Typ.subst Typ typ var acc)
  ;;

  let apply_subst_mono_context subst context =
    Map.map context ~f:(apply_subst subst)
  ;;

  let apply_subst_context subst context =
    Map.map context ~f:(fun poly_typ ->
      let (Poly (vars, typ)) = Abt.Poly_typ.out poly_typ in
      Abt.Poly_typ.poly (vars, apply_subst subst typ))
  ;;

  let rec free_vars ~bound_vars typ =
    match Abt.Typ.out typ with
    | Var var ->
      (match Set.mem bound_vars var with
       | true -> Abt.Typ.Var.Set.singleton var
       | false -> Abt.Typ.Var.Set.empty)
    | Arrow (typ1, typ2) -> Set.union (free_vars ~bound_vars typ1) (free_vars ~bound_vars typ2)
    | Prod l | Sum l ->
      List.map l ~f:(fun (_label, typ) -> free_vars ~bound_vars typ)
      |> Abt.Typ.Var.Set.union_list
    | Rec (var, typ) ->
      free_vars ~bound_vars:(Set.add bound_vars var) typ
  ;;

  let occurs ~in_ var =
    Set.mem (free_vars ~bound_vars:Abt.Typ.Var.Set.empty in_) var
  ;;

  let rec unify' bound_vars typ1 typ2 =
    match (Abt.Typ.out typ1, Abt.Typ.out typ2) with
    | Var var, _ when not (Set.mem bound_vars var)->
      (match occurs ~in_:typ2 var with
       | true -> failwith "type error"
       | false -> [ (typ2, var) ])
    | _, Var var when not (Set.mem bound_vars var) ->
      (match occurs ~in_:typ1 var with
       | true -> failwith "type error"
       | false -> [ (typ1, var) ])
    | Var var1, Var var2 ->
      (* We know from the above these are both bound, so we can't substitute for them. *)
      (match Abt.Typ.Var.equal var1 var2 with
       | true -> []
       | false -> failwith "type error")
    | Arrow (typ1, typ1'), Arrow (typ2, typ2') ->
      let subst = unify' bound_vars typ1 typ2 in
      let subst' = unify' bound_vars (apply_subst subst typ1') (apply_subst subst typ2') in
      subst @ subst'
    | (Prod l1, Prod l2) | (Sum l1, Sum l2) ->
      (* CR-soon wduff: Better errors. *)
      List.fold2_exn
        (List.sort l1 ~compare:[%compare: string * _])
        (List.sort l2 ~compare:[%compare: string * _])
        ~init:[]
        ~f:(fun acc_subst (label1, typ1) (label2, typ2) ->
          assert (String.equal label1 label2);
          let this_subst =
            unify' bound_vars (apply_subst acc_subst typ1) (apply_subst acc_subst typ2)
          in
          acc_subst @ this_subst)
    | Rec (var1, typ1), Rec (var2, typ2) ->
      unify'
        (Abt.Typ.Var.Set.add bound_vars var1)
        typ1
        (Abt.Typ.subst Typ (Abt.Typ.var var1) var2 typ2)
    | _ -> failwith "type error"
  ;;

  let unify typ1 typ2 = unify' Abt.Typ.Var.Set.empty typ1 typ2

  let don't_generalize typ = Abt.Poly_typ.poly ([], typ)

  let generalize context typ =
    let free_vars_in_context =
      Map.data context
      |> List.map ~f:(fun poly_typ ->
        let (Poly (bound_vars, typ)) = Abt.Poly_typ.out poly_typ in
        free_vars ~bound_vars:(Abt.Typ.Var.Set.of_list bound_vars) typ)
      |> Abt.Typ.Var.Set.union_list
    in
    let free_vars_in_typ = free_vars ~bound_vars:Abt.Typ.Var.Set.empty typ in
    let vars_to_generalize =
      Set.diff free_vars_in_typ free_vars_in_context
      |> Set.to_list
    in
    Abt.Poly_typ.poly (vars_to_generalize, typ)
  ;;

  let rec infer_for_pat (pat : Abt.Pat.t)
    : Abt.Typ.t Abt.Exp.Var.Map.t * Abt.Typ.t * Pat_constraint.Simple.t =
    match pat with
    | Wild -> (Abt.Exp.Var.Map.empty, Abt.Typ.var (Abt.Typ.Var.create "uvar"), True)
    | Var var ->
      let typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      (Abt.Exp.Var.Map.singleton var typ, typ, True)
    | Record fields ->
      let (context, fields_and_constrs) =
        List.fold_map fields ~init:Abt.Exp.Var.Map.empty
          ~f:(fun acc_context (label, pat) ->
            let (this_context, typ, constr) = infer_for_pat pat in
            (Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false),
             ((label, typ), (label, constr))))
      in
      let (fields, constrs) = List.unzip fields_and_constrs in
      (context, Abt.Typ.prod fields, Record constrs)
    | Inj _ | Fold _ -> failwithf "could not infer type of %s" (Abt.pat_to_string pat) ()
    | Ascribe (pat, typ) ->
      check_typ typ;
      match pat with
      | Inj (label, pat) ->
        (match Abt.Typ.out typ with
         | Sum clauses ->
           let (context, typ', constr) = infer_for_pat pat in
           (match
              List.find_map clauses ~f:(fun (label', typ'') ->
                Option.some_if (String.equal label label') typ'')
            with
            | None -> failwith "type error"
            | Some typ'' ->
              let subst = unify typ' typ'' in
              (apply_subst_mono_context subst context, typ, Inj (label, constr)))
         | _ -> failwith "type error")
      | Fold pat ->
        (match Abt.Typ.out typ with
         | Rec (typ_var, typ') ->
           let (context, typ'', constr) = infer_for_pat pat  in
           let subst = unify typ'' (Abt.Typ.subst Typ typ typ_var typ') in
           (apply_subst_mono_context subst context, typ, Fold constr)
         | _ -> failwith "type error")
      | _ ->
        let (context, typ', constr) = infer_for_pat pat in
        (* We don't need to return the substitution, only apply it to the local context, because all
           the variables being substituted for were generated by the above call to [infer_for_pat],
           and therefore can't occur in the outer expression context. We also don't need to apply it
           to [typ] before returning for essentially the same reason. *)
        let subst = unify typ' typ in
        (apply_subst_mono_context subst context, typ, constr)
  ;;

  let check_pat_exhaustive pat_constr ~wrt =
    match Pat_constraint.is_exhaustive pat_constr ~wrt with
    | true -> ()
    | false -> failwith "type error"
  ;;

  let rec infer_for_exp context exp =
    match Abt.Exp.out exp with
    | Let_type _ -> assert false
    | Var var ->
      let (Poly (_, typ)) = Abt.Poly_typ.out (Map.find_exn context var) in
      ([], typ)
    | Fun (arg_pat, body) ->
      let (pat_context, arg_typ, pat_constr) = infer_for_pat arg_pat in
      check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:arg_typ;
      let pat_context = Map.map pat_context ~f:don't_generalize in
      let context =
        Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
      in
      let (subst, result_typ) = infer_for_exp context body in
      (subst, Abt.Typ.arrow (apply_subst subst arg_typ, result_typ))
    | Ap (func, arg) ->
      let (subst1, func_typ) = infer_for_exp context func in
      let (subst2, arg_typ) = infer_for_exp (apply_subst_context subst1 context) arg in
      let result_typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      let subst3 = unify (apply_subst subst2 func_typ) (Abt.Typ.arrow (arg_typ, result_typ)) in
      (subst1 @ subst2 @ subst3, apply_subst subst3 result_typ)
    | Record fields ->
      let (subst, fields) =
        List.fold_map fields ~init:[] ~f:(fun acc_subst (label, exp) ->
          let (this_subst, typ) = infer_for_exp (apply_subst_context acc_subst context) exp in
        (acc_subst @ this_subst, (label, typ)))
      in
      (subst, Abt.Typ.prod fields)
    | Match (exp, cases) ->
      let (subst, typ) = infer_for_exp context exp in
      let result_typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      let ((subst, _context, result_typ), pat_constrs) =
        List.fold_map cases ~init:(subst, apply_subst_context subst context, result_typ)
          ~f:(fun (acc_subst, context, result_typ) (pat, exp) ->
            let (pat_context, pat_typ, pat_constr) = infer_for_pat pat in
            let pat_context = Map.map pat_context ~f:don't_generalize in
            let context =
              Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
            in
            let subst1 = unify typ pat_typ in
            let context = apply_subst_context subst1 context in
            let (subst2, result_typ') = infer_for_exp context exp in
            let subst3 = unify (apply_subst (subst1 @ subst2) result_typ) result_typ' in
            ((acc_subst @ subst1 @ subst2 @ subst3,
              apply_subst_context (subst2 @ subst3) context,
              apply_subst subst3 result_typ'),
             pat_constr))
      in
      (match Pat_constraint.or_list_check_irredundant pat_constrs ~wrt:typ with
       | None -> failwith "redundant pattern"
       | Some pat_constr ->
         check_pat_exhaustive pat_constr ~wrt:typ;
         (subst, result_typ))
    | Fix (var, body) ->
      let typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      let (subst1, typ') =
        infer_for_exp (Map.set context ~key:var ~data:(Abt.Poly_typ.poly ([], typ))) body
      in
      let subst2 = unify (apply_subst subst1 typ) typ' in
      (subst1 @ subst2, apply_subst subst2 typ')
    | Let ((pat, exp1), exp2) ->
      let (subst1, typ1) = infer_for_exp context exp1 in
      let (pat_context, pat_typ, pat_constr) = infer_for_pat pat in
      check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:pat_typ;
      let subst2 = unify typ1 pat_typ in
      let context = apply_subst_context (subst1 @ subst2) context in
      let pat_context = apply_subst_mono_context subst2 pat_context in
      (* CR wduff: Consider the value restriction. *)
      let pat_context = Map.map pat_context ~f:(generalize context) in
      let context =
        Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
      in
      let (subst3, typ2) = infer_for_exp context exp2 in
      (subst1 @ subst2 @ subst3, typ2)
    | Inj _ | Fold _ -> failwithf "could not infer type of %s" (Abt.exp_to_string exp) ()
    | Ascribe (exp, typ) ->
      check_typ typ;
      match Abt.Exp.out exp with
      | Inj (label, exp) ->
        (match Abt.Typ.out typ with
         | Sum clauses ->
           let (subst1, typ') = infer_for_exp context exp in
           (match
              List.find_map clauses ~f:(fun (label', typ'') ->
                Option.some_if (String.equal label label') typ'')
            with
            | None -> failwith "type error"
            | Some typ'' ->
              let subst2 = unify typ' typ'' in
              (subst1 @ subst2, typ))
         | _ -> failwith "type error")
      | Fold exp ->
        (match Abt.Typ.out typ with
         | Rec (typ_var, typ') ->
           let (subst1, typ'') = infer_for_exp context exp in
           let subst2 = unify typ'' (Abt.Typ.subst Typ typ typ_var typ') in
           (subst1 @ subst2, typ)
         | _ -> failwith "type error")
      | _ ->
        let (subst1, typ') = infer_for_exp context exp in
        (* We don't need to substitute into typ, because it is from the source program and therefore
           can't contain unification variables. *)
        let subst2 = unify typ' typ in
        (subst1 @ subst2, typ)
  ;;

  let run_exn exp =
    let exp = eval_type_aliases exp in
    let (_, typ) = infer_for_exp Abt.Exp.Var.Map.empty exp in
    typ
  ;;
end

let run ~filename ~type_checker () =
  let ast =
    In_channel.with_file filename ~f:(fun in_channel ->
      let lexbuf = Lexing.from_channel in_channel in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      Parser.program Lexer.token lexbuf)
  in
  let abt = Abt_of_ast.convert ast in
  printf "%s\n%!" (Abt.exp_to_string abt);
  (match type_checker with
   | `None -> ()
   | `Bidirectional ->
     printf "%s\n%!" (Abt.typ_to_string (Bidirectional_type_checker.run_exn abt))
   | `Hindley_milner ->
     printf "%s\n%!" (Abt.typ_to_string (Hindley_milner_type_checker.run_exn abt)));
  printf "%s\n%!" (Abt.exp_to_string (Dynamics.eval abt))
;;

let type_checker_arg_type =
  Command.Arg_type.of_alist_exn
    [ ("none", `None)
    ; ("bidirectional", `Bidirectional)
    ; ("hindley-milner", `Hindley_milner)
    ]
;;

let command =
  Command.basic
    ~summary:"Interprets fpcpat programs"
    (let%map_open.Command () = return ()
     and filename = anon ("FILE" %: Filename.arg_type)
     and type_checker =
       flag "type-checker" (required type_checker_arg_type)
         ~doc:" which type checker to use (none|bidirectional|hindley-milner)"
     in
     fun () -> run ~filename ~type_checker ())
;;
