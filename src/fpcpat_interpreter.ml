open! Core

module Ast = Fpcpat_parse_tree

module Abt =
  Abbot_other_examples.Fpcpat.Make (struct
    type t = string [@@deriving sexp_of]
  end)

let rec typ_to_string (typ : Abt.Typ.t) =
  match Abt.Typ.out typ with
  | Var var -> Abt.Typ.Var.name var
  | Arrow (typ1, typ2) -> sprintf "(%s -> %s)" (typ_to_string typ1) (typ_to_string typ2)
  | Prod fields ->
    List.map fields ~f:(fun (label, typ) -> sprintf "%s : %s" label (typ_to_string typ))
    |> String.concat ~sep:", "
    |> sprintf "prod[%s]"
  | Sum clauses ->
    List.map clauses ~f:(fun (label, typ) -> sprintf "%s : %s" label (typ_to_string typ))
    |> String.concat ~sep:", "
    |> sprintf "sum[%s]"
  | Rec (var, typ) -> sprintf "rec[%s.%s]" (Abt.Typ.Var.name var) (typ_to_string typ)
;;

let record_to_string to_string fields =
  match fields with
  | [] -> "{}"
  | _::_ ->
    List.map fields ~f:(fun (label, x) ->
      sprintf "%s = %s" label (to_string x))
    |> String.concat ~sep:", "
    |> sprintf "{ %s }"
;;

let rec pat_to_string (pat : Abt.Pat.t) =
  match pat with
  | Wild -> "_"
  | Var var -> Abt.Exp.Var.name var
  | Record fields -> record_to_string pat_to_string fields
  | Inj (label, pat) -> sprintf "(inj[%s] %s)" label (pat_to_string pat)
  | Fold pat -> sprintf "(fold %s)" (pat_to_string pat)
  | Ascribe (pat, typ) -> sprintf "(%s : %s)" (pat_to_string pat) (typ_to_string typ)
;;

(* CR wduff: Consider removing superfluous parens. *)
let rec exp_to_string (exp : Abt.Exp.t) =
  match Abt.Exp.out exp with
  | Var var -> Abt.Exp.Var.name var
  | Fun (arg_pat, body) ->
    sprintf "(fun (%s) => %s)" (pat_to_string arg_pat) (exp_to_string body)
  | Ap (func, arg) ->
    sprintf "(%s %s)" (exp_to_string func) (exp_to_string arg)
  | Record fields ->
    record_to_string exp_to_string fields
  | Inj (label, exp) -> sprintf "(inj[%s] %s)" label (exp_to_string exp)
  | Fold exp -> sprintf "(fold %s)" (exp_to_string exp)
  | Match (exp, cases) ->
    (match cases with
     | [] -> sprintf "match %s with end" (exp_to_string exp)
     | _::_ ->
       List.map cases ~f:(fun (pat, exp) ->
         sprintf "%s => %s" (pat_to_string pat) (exp_to_string exp))
       |> String.concat ~sep:" | "
       |> sprintf "match %s with %s end" (exp_to_string exp))
  | Fix (var, body) ->
    sprintf "(fix %s is %s)" (Abt.Exp.Var.name var) (exp_to_string body)
  | Let ((pat, exp1), exp2) ->
    sprintf "(let %s = %s in %s)" (pat_to_string pat) (exp_to_string exp1) (exp_to_string exp2)
  | Let_type ((typ_var, typ), exp) ->
    sprintf
      "(let type %s = %s in %s)"
      (Abt.Typ.Var.name typ_var)
      (typ_to_string typ)
      (exp_to_string exp)
  | Ascribe (exp, typ) ->
    sprintf "(%s : %s)" (exp_to_string exp) (typ_to_string typ)
;;

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
    | Prod fields ->
      Abt.Typ.prod
        (List.map fields ~f:(fun (label, typ) ->
           (label, convert_typ context typ)))
    | Sum clauses ->
      Abt.Typ.sum
        (List.map clauses ~f:(fun (label, typ) ->
           (label, convert_typ context typ)))
    | Rec (var_name, typ) ->
      let var = Abt.Typ.Var.create var_name in
      let context = String.Map.set context ~key:var_name ~data:var in
      Abt.Typ.rec_ (var, convert_typ context typ)
  ;;

  let rec convert_pat typ_context
    : Ast.Pat.t -> Abt.Exp.Var.t String.Map.t * Abt.Pat.t = function
    | Wild -> (String.Map.empty, Wild)
    | Var var_name ->
      let var = Abt.Exp.Var.create var_name in
      let context = String.Map.singleton var_name var in
      (context, Var var)
    | Record fields ->
      let (context, fields) =
        List.fold_map fields ~init:String.Map.empty ~f:(fun acc_context (label, pat) ->
          let (this_context, pat) = convert_pat typ_context pat in
          let context =
            Map.merge_skewed acc_context this_context ~combine:(fun ~key:var_name _var1 _var2 ->
              (* CR wduff: Location info would be nice. *)
              raise_s [%message "Duplicate variable name in pattern." (var_name : string)])
          in
          (context, (label, pat)))
      in
      (context, Record fields)
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
      Abt.Exp.record
        (List.map fields ~f:(fun (label, exp) ->
           (label, convert_exp typ_context context exp)))
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
    (* CR wduff: It's kinda sad that abbot doesn't give us a way to build up a big subst
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
       | _ -> raise_s [%message (exp_to_string exp : string)])
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

(* CR wduff: Think about error messages. *)
module Bidirectional_type_checker : sig
  val run_exn : Abt.Exp.t -> Abt.Typ.t
end = struct
  (* CR wduff: We do need to make sure to check for duplicate labels in that pass. *)
  (* This is good to have for completeness, but it doesn't actually have to do anything because we
     already check that types are well-formed in the ast->abt pass. Also this really is "check" not
     "synth", because we need these types ot have kind "type", since they come from annotations. *)
  let check_typ (_ : Abt.Typ.t) = ()

  (* CR wduff: We could also check for empty types, which can be considered subtypes of any other
     type, and functions out of bottom, which can be considered supertypes of any other type. *)
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
      (* CR wduff: This is not the most complete way to do this. *)
      subtype typ (Abt.Typ.subst Typ (Abt.Typ.var var) var' typ')
    | _ -> failwith "type error"
  ;;

  let rec synth_pat (pat : Abt.Pat.t) =
    match pat with
    | Record fields ->
      let (context, field_typs) =
        List.fold_map fields ~init:Abt.Exp.Var.Map.empty ~f:(fun acc_context (label, pat) ->
          let (this_context, typ) = synth_pat pat in
          let context =
            Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false)
          in
          (context, (label, typ)))
      in
      (context, Abt.Typ.prod field_typs)
    | Ascribe (pat, typ) ->
      check_typ typ;
      let context = check_pat pat typ in
      (context, typ)
    | _ -> failwithf "could not infer type of %s" (pat_to_string pat) ()

  and check_pat (pat : Abt.Pat.t) typ =
    match pat with
    | Wild -> Abt.Exp.Var.Map.empty
    | Var var -> Abt.Exp.Var.Map.singleton var typ
    | Record fields ->
      (match Abt.Typ.out typ with
       | Prod field_typs ->
         (* CR wduff: Probably we should give an error message for duplicate field names, rather
            than raising? *)
         let field_typs = String.Table.of_alist_exn field_typs in
         (* CR wduff: Complain about missing fields? They are safe, but indicate dead code. *)
         (* CR wduff: Check for duplicate field names in the pattern, if we're not doing that in the
            ast->abt pass. *)
         List.fold fields ~init:Abt.Exp.Var.Map.empty ~f:(fun acc_context (label, pat) ->
           match Hashtbl.find field_typs label with
           | Some typ ->
             let this_context = check_pat pat typ in
             Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false)
           | None -> failwith "type error")
       | _ -> failwith "type error")
    | Inj (label, pat) ->
      (match Abt.Typ.out typ with
       | Sum clause_typs -> (match
         List.find_map clause_typs ~f:(fun (label', typ) ->
           match String.equal label label' with
           | true -> Some typ
           | false -> None)
       with
       | Some typ -> check_pat pat typ
       | None ->
         (* CR wduff: Isn't this case actually just fine? *)
         failwith "type error")
         | _ -> failwith "type error")
    | Fold pat ->
      (match Abt.Typ.out typ with
       | Rec (typ_var, typ') -> check_pat pat (Abt.Typ.subst Typ typ typ_var typ')
       | _ -> failwith "type error")
    | _ ->
      let (context, typ') = synth_pat pat in
      subtype typ typ';
      context
  ;;

  let synth_pat_and_extend_context context pat =
    let (pat_context, typ) = synth_pat pat in
    let context =
      Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
    in
    (context, typ)
  ;;

  let check_pat_and_extend_context context pat typ =
    let pat_context = check_pat pat typ in
    let context =
      Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
    in
    context
  ;;

  let rec synth_exp context exp =
    match Abt.Exp.out exp with
    | Var var ->
      (try Map.find_exn context var
       with exn -> raise_s [%message "hrm" (exn : exn) (context : Abt.Typ.t Abt.Exp.Var.Map.t)])
    | Fun (arg_pat, body) ->
      let (context, arg_typ) = synth_pat_and_extend_context context arg_pat in
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
      (* CR wduff: This non-determinism is sad, but hopefully most patterns are small, so this won't
         be too expensive. *)
      (match synth_pat_and_extend_context context pat with
       | (context', typ) ->
         check_exp context exp1 typ;
         synth_exp context' exp2
       | exception _ ->
         let typ1 = synth_exp context exp1 in
         let context = check_pat_and_extend_context context pat typ1 in
         synth_exp context exp2)
    | Ascribe (exp, typ) ->
      check_typ typ;
      check_exp context exp typ;
      typ
    | _ -> failwithf "could not infer type of %s" (exp_to_string exp) ()

  and check_exp context exp typ =
    (* CR wduff: We could allow "wildcard" types, and deal with them by switching from checking back
       to synthesizing when checking against a wildcard. This would allow users to, e.g., only
       specify the argument type of a function, though they can do that with patter ascriptions as
       well. *)
    match Abt.Exp.out exp with
    | Fun (arg_pat, body) ->
      (* CR wduff: There should be a synth version of this that attempts to synthesize the type of
         the pattern. *)
      (match Abt.Typ.out typ with
       | Arrow (typ1, typ2) ->
         let context = check_pat_and_extend_context context arg_pat typ1 in
         check_exp context body typ2
       | _ -> failwith "type error")
    | Record fields ->
      (* CR wduff: Check for duplicate field names, if we're not doing that above. (and also in the
         synth code). *)
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
      (* CR wduff: Can there be a synth version of this? *)
      (match Abt.Typ.out typ with
       | Rec (typ_var, typ') ->
         check_exp context exp (Abt.Typ.subst Typ typ typ_var typ')
       | _ -> failwith "type error")
    | Match (exp, cases) ->
      let typ' = synth_exp context exp in
      List.iter cases ~f:(fun (pat, exp) ->
        let context = check_pat_and_extend_context context pat typ' in
        check_exp context exp typ)
    | Fix (var, body) ->
      check_exp (Map.set context ~key:var ~data:typ) body typ
    | Let ((pat, exp1), exp2) ->
      (match synth_pat_and_extend_context context pat with
       | (context', typ') ->
         check_exp context exp1 typ';
         check_exp context' exp2 typ
       | exception _ ->
         let typ1 = synth_exp context exp1 in
         let context = check_pat_and_extend_context context pat typ1 in
         check_exp context exp2 typ)
    | _ ->
      let typ' = synth_exp context exp in
      subtype typ' typ
  ;;

  let run_exn exp =
    let exp = eval_type_aliases exp in
    synth_exp Abt.Exp.Var.Map.empty exp
  ;;
end

module Hindley_milner_type_checker : sig
  val run_exn : Abt.Exp.t -> Abt.Typ.t
end = struct
  let apply_subst subst typ =
    List.fold subst ~init:typ ~f:(fun acc (typ, var) -> Abt.Typ.subst Typ typ var acc)
  ;;

  let apply_subst_context subst context =
    Abt.Exp.Var.Map.map context ~f:(fun poly_typ ->
      let (Poly (vars, typ)) = Abt.Poly_typ.out poly_typ in
      Abt.Poly_typ.poly (vars, apply_subst subst typ))
  ;;

  let rec unify typ1 typ2 =
    match (Abt.Typ.out typ1, Abt.Typ.out typ2) with
    (* CR wduff: We need an occurs check in these two cases. *)
    | Var var, _ -> [ (typ2, var) ]
    | _, Var var -> [ (typ1, var) ]
    | Arrow (typ1, typ1'), Arrow (typ2, typ2') ->
      let subst = unify typ1 typ2 in
      let subst' = unify (apply_subst subst typ1') (apply_subst subst typ2') in
      subst @ subst'
    | Prod fields1, Prod fields2 ->
      unify_lists fields1 fields2
    | Sum clauses1, Sum clauses2 ->
      unify_lists clauses1 clauses2
    | Rec (var1, typ1), Rec (var2, typ2) ->
      (* CR wduff: Figure out what to do here. *)
      failwith "unimpl"
    | _ -> failwith "type error"

  and unify_lists l1 l2 =
    (* CR wduff: Better errors. *)
    List.fold2_exn
      (List.sort l1 ~compare:[%compare: string * _])
      (List.sort l2 ~compare:[%compare: string * _])
      ~init:[]
      ~f:(fun acc_subst (label1, typ1) (label2, typ2) ->
        assert (String.equal label1 label2);
        (* CR wduff: Do we have to compose the substs? *)
        let this_subst = unify (apply_subst acc_subst typ1) (apply_subst acc_subst typ2) in
        (* CR wduff: Order could matter, and I think this is the wrong order. *)
        this_subst @ acc_subst)
  ;;

  let rec infer_pat (pat : Abt.Pat.t) =
    match pat with
    | Wild -> ([], Abt.Exp.Var.Map.empty, Abt.Typ.var (Abt.Typ.Var.create "uvar"))
    | Var var ->
      let typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      ([], Abt.Exp.Var.Map.singleton var (Abt.Poly_typ.poly ([], typ)), typ)
    | Record fields ->
      let ((subst, context), fields) =
        List.fold_map fields ~init:([], Abt.Exp.Var.Map.empty)
          ~f:(fun (acc_subst, acc_context) (label, pat) ->
            let (this_subst, this_context, typ) = infer_pat pat in
            (* CR wduff: Order could matter, and I think this is the wrong order. *)
            ((this_subst @ acc_subst,
              Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false)),
             (label, typ)))
      in
      (subst, context, Abt.Typ.prod fields)
    | Inj (label, pat) -> ()
    | Fold pat -> ()
    | Ascribe (pat, typ) ->
      (* CR wduff: Check that [typ] is well-formed first. *)
      let (subst1, context, typ') = infer_pat pat in
      (* We don't need to substitute into typ, because it is from the source program and therefore
         can't contain unification variables. *)
      let subst2 = unify typ' typ in
      (subst1 @ subst2, apply_subst_context subst2 context, typ)

  let rec infer_exp context exp =
    match Abt.Exp.out exp with
    | Let_type _ -> assert false
    | Var var ->
      let (Poly (_, typ)) = Abt.Poly_typ.out (Map.find_exn context var) in
      ([], typ)
    | Fun (arg_pat, body) ->
      let (subst1, pat_context, arg_typ) = infer_pat arg_pat in
      let context =
        Map.merge_skewed
          (apply_subst_context subst1 context)
          pat_context
          ~combine:(fun ~key:_ _ _ -> assert false)
      in
      let (subst2, result_typ) = infer_exp context body in
      (subst1 @ subst2, Abt.Typ.arrow (apply_subst subst2 arg_typ, result_typ))
    | Ap (func, arg) ->
      let (subst1, func_typ) = infer_exp context func in
      let (subst2, arg_typ) = infer_exp (apply_subst_context subst1 context) arg in
      let result_typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      let subst3 = unify (apply_subst subst2 func_typ) (Abt.Typ.arrow (arg_typ, result_typ)) in
      (subst1 @ subst2 @ subst3, apply_subst subst3 result_typ)
    | Record fields ->
      let (subst, fields) =
        List.fold_map fields ~init:[] ~f:(fun acc_subst (label, exp) ->
          let (this_subst, typ) = infer_exp (apply_subst_context acc_subst context) exp in
        (* CR wduff: Order could matter, and I think this is the wrong order. *)
        (this_subst @ acc_subst, (label, typ)))
      in
      (subst, Abt.Typ.prod fields)
    | Inj (label, exp) -> ()
    | Fold exp -> ()
    | Match (exp, cases) ->
      let (subst, typ) = infer_exp context exp in
      let result_typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      List.fold cases ~init:(subst, result_typ)
        (* CR wduff: Need to keep changing context across the fold as well. *)
        ~f:(fun (acc_subst, result_typ) (pat, exp) ->
          let (subst1, pat_context, pat_typ) = infer_pat pat in
          let subst2 = unify typ pat_typ in
          let context =
            Map.merge_skewed
              (apply_subst_context (subst1 @ subst2) context)
              (apply_subst_context subst2 pat_context)
              ~combine:(fun ~key:_ _ _ -> assert false)
          in
          let (subst3, result_typ') = infer_exp context exp in
          let subst4 = unify (apply_subst (subst1 @ subst2 @ subst3) result_typ) result_typ' in
          (acc_subst @ subst1 @ subst2 @ subst3 @ subst4, apply_subst subst4 result_typ'))
    | Fix (var, body) ->
      let typ = Abt.Typ.var (Abt.Typ.Var.create "uvar") in
      let (subst1, typ') =
        infer_exp (Map.set context ~key:var ~data:(Abt.Poly_typ.poly ([], typ))) body
      in
      let subst2 = unify (apply_subst subst1 typ) typ' in
      (subst1 @ subst2, apply_subst subst2 typ')
    | Let ((pat, exp1), exp2) ->
      let (subst1, typ1) = infer_exp context exp1 in
      let (subst2, pat_context, pat_typ) = infer_pat pat in
      let subst3 = unify (apply_subst subst2 typ1) pat_typ in
      (* CR wduff: We need to generalize here, and consider the value restriction. *)
      let context =
        Map.merge_skewed
          (apply_subst_context (subst1 @ subst2) context)
          pat_context
          ~combine:(fun ~key:_ _ _ -> assert false)
      in
      let (subst4, typ2) = infer_exp (apply_subst_context subst3 context) exp2 in
      (subst1 @ subst2 @ subst3 @ subst4, typ2)
    | Ascribe (exp, typ) ->
      (* CR wduff: Check that [typ] is well-formed first. *)
      let (subst1, typ') = infer_exp context exp in
      (* We don't need to substitute into typ, because it is from the source program and therefore
         can't contain unification variables. *)
      let subst2 = unify typ' typ in
      (subst1 @ subst2, typ)
  ;;

  let run_exn exp =
    let exp = eval_type_aliases exp in
    let (_, typ) = infer_exp Abt.Exp.Var.Map.empty exp in
    typ
  ;;
end

let run ~filename () =
  let ast =
    In_channel.with_file filename ~f:(fun in_channel ->
      let lexbuf = Lexing.from_channel in_channel in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      Fpcpat_parser.program Fpcpat_lexer.token lexbuf)
  in
  let abt = Abt_of_ast.convert ast in
  printf "%s\n%!" (exp_to_string abt);
  printf "%s\n%!" (typ_to_string (Bidirectional_type_checker.run_exn abt));
  printf "%s\n%!" (exp_to_string (Dynamics.eval abt))
;;

let command =
  Command.basic
    ~summary:"Interprets fpcpat programs"
    (let%map_open.Command () = return ()
     and filename = anon ("FILE" %: Filename.arg_type)
     in
     fun () -> run ~filename ())
;;
