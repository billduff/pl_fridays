open! Core
open Abt
open Type_checker_shared

(* This is good to have for completeness, but it doesn't actually have to do anything because we
   already check that types are well-formed in the ast->abt pass. Also this really is "check" not
   "synth", because we need these types to have kind "type", since they come from annotations. *)
let check_typ (_ : Typ.t) = ()

(* CR-soon wduff: This subtyping relation is incomplete in a couple ways:
   1) The way we deal with recursive types is not fully general.
   2) We could consider whether types are inhabited (by values), and take advantage of the
   fact that empty types can be considered subtypes of any other type and functions out of the
   empty type can be considered supertypes of any other type.

   I haven't done (1) because it's really grotty to implement, espcially if you try to implement
   it efficiently.

   I haven't done (2) because I'm dubious whether relying on type inhabitedness is a good idea,
   since it is often undecidable (e.g. for system F).

   A subtyping algorithm that solves both of these is given here:
   https://www.cse.usf.edu/~ligatti/papers/subIsoTR.pdf *)
let rec subtype typ typ' =
  match (Typ.out typ, Typ.out typ') with
  | (Var var, Var var') ->
    (match Typ.Var.equal var var' with
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
    subtype typ (Typ.subst Typ (Typ.var var) var' typ')
  | _ -> failwith "type error"
;;

let rec synth_pat (pat : Pat.t)
  : Typ.t Exp.Var.Map.t * Typ.t * Pat_constraint.Simple.t =
  match pat with
  | Record fields ->
    let (context, field_typs_and_constrs) =
      List.fold_map fields ~init:Exp.Var.Map.empty ~f:(fun acc_context (label, pat) ->
        let (this_context, typ, constr) = synth_pat pat in
        let context =
          Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false)
        in
        (context, ((label, typ), (label, constr))))
    in
    let (field_typs, field_constrs) = List.unzip field_typs_and_constrs in
    (context, Typ.prod field_typs, Record field_constrs)
  | Inj (label, pat) ->
    let (context, typ, constr) = synth_pat pat in
    (context, Typ.sum [ (label, typ) ], Inj (label, constr))
  | Ascribe (pat, typ) ->
    check_typ typ;
    let (context, constr) = check_pat pat typ in
    (context, typ, constr)
  | Wild | Var _ | Fold _ -> failwithf "could not infer type of %s" (pat_to_string pat) ()

and check_pat (pat : Pat.t) typ =
  match pat with
  | Wild -> (Exp.Var.Map.empty, True)
  | Var var -> (Exp.Var.Map.singleton var typ, True)
  | Record fields ->
    (match Typ.out typ with
     | Prod field_typs ->
       let field_typs = String.Table.of_alist_exn field_typs in
       let (context, field_constrs) =
         (* Note: We deliberately allow fields that show up in the type to be missing from the
            pattern. This is important for subsumption. E.g., if we have a variable bound with
            some record type, and we're matching on that variable, we need the program to continue
            to type check if an expression with a smaller principle type is substituted for the
            variable. *)
         List.fold_map fields ~init:Exp.Var.Map.empty ~f:(fun acc_context (label, pat) ->
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
    (match Typ.out typ with
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
    (match Typ.out typ with
     | Rec (typ_var, typ') ->
       let (context, constr) = check_pat pat (Typ.subst Typ typ typ_var typ') in
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
  | false -> failwith "non-exhaustive pattern match"
;;

let rec synth_exp context exp =
  match Exp.out exp with
  | Var var ->
    (try Map.find_exn context var
     with exn -> raise_s [%message "hrm" (exn : exn) (context : Typ.t Exp.Var.Map.t)])
  | Fun (arg_pat, body) ->
    let (context, arg_typ, pat_constr) = synth_pat_and_extend_context context arg_pat in
    check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:arg_typ;
    Typ.arrow (arg_typ, synth_exp context body)
  | Ap (func, arg) ->
    (match Typ.out (synth_exp context func) with
     | Arrow (arg_typ, result_typ) ->
       check_exp context arg arg_typ;
       result_typ
     | _ -> failwith "type error")
  | Record fields ->
    List.map fields ~f:(fun (label, exp) ->
      (label, synth_exp context exp))
    |> Typ.prod
  | Inj (label, exp) ->
    let typ = synth_exp context exp in
    Typ.sum [ (label, typ) ]
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
  | Fold _ | Match _ | Fix _ -> failwithf "could not infer type of %s" (exp_to_string exp) ()
  | Let_type _ -> assert false

and check_exp context exp typ =
  (* CR-soon wduff: We could allow "wildcard" types, and deal with them by switching from checking
     back to synthesizing when checking against a wildcard. This would allow users to, e.g., only
     specify the argument type of a function, though they can do that with patter ascriptions as
     well. *)
  match Exp.out exp with
  | Fun (arg_pat, body) ->
    (match Typ.out typ with
     | Arrow (typ1, typ2) ->
       let (context, pat_constr) = check_pat_and_extend_context context arg_pat typ1 in
       check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:typ1;
       check_exp context body typ2
     | _ -> failwith "type error")
  | Record fields ->
    (match Typ.out typ with
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
              ignore (synth_exp context exp : Typ.t);
              None
            | `Right _ -> failwith "type error")
          : Nothing.t String.Map.t)
     | _ -> failwith "type error")
  | Inj (label, exp) ->
    (match Typ.out typ with
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
    (match Typ.out typ with
     | Rec (typ_var, typ') ->
       check_exp context exp (Typ.subst Typ typ typ_var typ')
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

let typecheck_exn exp =
  let exp = eval_type_aliases exp in
  synth_exp Exp.Var.Map.empty exp
;;
