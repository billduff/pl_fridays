open! Core
open Abt
open Type_checker_shared

let check_typ (_ : Typ.t) = ()

let apply_subst subst typ =
  List.fold subst ~init:typ ~f:(fun acc (typ, var) -> Typ.subst Typ typ var acc)
;;

let apply_subst_mono_context subst context =
  Map.map context ~f:(apply_subst subst)
;;

let apply_subst_context subst context =
  Map.map context ~f:(fun poly_typ ->
    let (Poly (vars, typ)) = Poly_typ.out poly_typ in
    Poly_typ.poly (vars, apply_subst subst typ))
;;

let rec free_vars ~bound_vars typ =
  match Typ.out typ with
  | Var var ->
    (match Set.mem bound_vars var with
     | true -> Typ.Var.Set.singleton var
     | false -> Typ.Var.Set.empty)
  | Arrow (typ1, typ2) -> Set.union (free_vars ~bound_vars typ1) (free_vars ~bound_vars typ2)
  | Prod l | Sum l ->
    List.map l ~f:(fun (_label, typ) -> free_vars ~bound_vars typ)
    |> Typ.Var.Set.union_list
  | Rec (var, typ) ->
    free_vars ~bound_vars:(Set.add bound_vars var) typ
;;

let occurs ~in_ var =
  Set.mem (free_vars ~bound_vars:Typ.Var.Set.empty in_) var
;;

let rec unify' bound_vars typ1 typ2 =
  match (Typ.out typ1, Typ.out typ2) with
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
    (match Typ.Var.equal var1 var2 with
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
      (Typ.Var.Set.add bound_vars var1)
      typ1
      (Typ.subst Typ (Typ.var var1) var2 typ2)
  | _ -> failwith "type error"
;;

let unify typ1 typ2 = unify' Typ.Var.Set.empty typ1 typ2

let don't_generalize typ = Poly_typ.poly ([], typ)

let generalize context typ =
  let free_vars_in_context =
    Map.data context
    |> List.map ~f:(fun poly_typ ->
      let (Poly (bound_vars, typ)) = Poly_typ.out poly_typ in
      free_vars ~bound_vars:(Typ.Var.Set.of_list bound_vars) typ)
    |> Typ.Var.Set.union_list
  in
  let free_vars_in_typ = free_vars ~bound_vars:Typ.Var.Set.empty typ in
  let vars_to_generalize =
    Set.diff free_vars_in_typ free_vars_in_context
    |> Set.to_list
  in
  Poly_typ.poly (vars_to_generalize, typ)
;;

let rec infer_for_pat (pat : Pat.t)
  : Typ.t Exp.Var.Map.t * Typ.t * Pat_constraint.Simple.t =
  match pat with
  | Wild -> (Exp.Var.Map.empty, Typ.var (Typ.Var.create "uvar"), True)
  | Var var ->
    let typ = Typ.var (Typ.Var.create "uvar") in
    (Exp.Var.Map.singleton var typ, typ, True)
  | Record fields ->
    let (context, fields_and_constrs) =
      List.fold_map fields ~init:Exp.Var.Map.empty
        ~f:(fun acc_context (label, pat) ->
          let (this_context, typ, constr) = infer_for_pat pat in
          (Map.merge_skewed acc_context this_context ~combine:(fun ~key:_ _ _ -> assert false),
           ((label, typ), (label, constr))))
    in
    let (fields, constrs) = List.unzip fields_and_constrs in
    (context, Typ.prod fields, Record constrs)
  | Inj _ | Fold _ -> failwithf "could not infer type of %s" (pat_to_string pat) ()
  | Ascribe (pat, typ) ->
    check_typ typ;
    match pat with
    | Inj (label, pat) ->
      (match Typ.out typ with
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
      (match Typ.out typ with
       | Rec (typ_var, typ') ->
         let (context, typ'', constr) = infer_for_pat pat  in
         let subst = unify typ'' (Typ.subst Typ typ typ_var typ') in
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
  match Exp.out exp with
  | Let_type _ -> assert false
  | Var var ->
    let (Poly (_, typ)) = Poly_typ.out (Map.find_exn context var) in
    ([], typ)
  | Fun (arg_pat, body) ->
    let (pat_context, arg_typ, pat_constr) = infer_for_pat arg_pat in
    check_pat_exhaustive (Pat_constraint.singleton pat_constr) ~wrt:arg_typ;
    let pat_context = Map.map pat_context ~f:don't_generalize in
    let context =
      Map.merge_skewed context pat_context ~combine:(fun ~key:_ _ _ -> assert false)
    in
    let (subst, result_typ) = infer_for_exp context body in
    (subst, Typ.arrow (apply_subst subst arg_typ, result_typ))
  | Ap (func, arg) ->
    let (subst1, func_typ) = infer_for_exp context func in
    let (subst2, arg_typ) = infer_for_exp (apply_subst_context subst1 context) arg in
    let result_typ = Typ.var (Typ.Var.create "uvar") in
    let subst3 = unify (apply_subst subst2 func_typ) (Typ.arrow (arg_typ, result_typ)) in
    (subst1 @ subst2 @ subst3, apply_subst subst3 result_typ)
  | Record fields ->
    let (subst, fields) =
      List.fold_map fields ~init:[] ~f:(fun acc_subst (label, exp) ->
        let (this_subst, typ) = infer_for_exp (apply_subst_context acc_subst context) exp in
        (acc_subst @ this_subst, (label, typ)))
    in
    (subst, Typ.prod fields)
  | Match (exp, cases) ->
    let (subst, typ) = infer_for_exp context exp in
    let result_typ = Typ.var (Typ.Var.create "uvar") in
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
    let typ = Typ.var (Typ.Var.create "uvar") in
    let (subst1, typ') =
      infer_for_exp (Map.set context ~key:var ~data:(Poly_typ.poly ([], typ))) body
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
  | Inj _ | Fold _ -> failwithf "could not infer type of %s" (exp_to_string exp) ()
  | Ascribe (exp, typ) ->
    check_typ typ;
    match Exp.out exp with
    | Inj (label, exp) ->
      (match Typ.out typ with
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
      (match Typ.out typ with
       | Rec (typ_var, typ') ->
         let (subst1, typ'') = infer_for_exp context exp in
         let subst2 = unify typ'' (Typ.subst Typ typ typ_var typ') in
         (subst1 @ subst2, typ)
       | _ -> failwith "type error")
    | _ ->
      let (subst1, typ') = infer_for_exp context exp in
      (* We don't need to substitute into typ, because it is from the source program and therefore
         can't contain unification variables. *)
      let subst2 = unify typ' typ in
      (subst1 @ subst2, typ)
;;

let typecheck_exn exp =
  let exp = eval_type_aliases exp in
  let (_, typ) = infer_for_exp Exp.Var.Map.empty exp in
  typ
;;
