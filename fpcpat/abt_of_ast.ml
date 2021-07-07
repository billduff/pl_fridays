open! Core

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
