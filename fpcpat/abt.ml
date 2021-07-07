open! Core

module Label = struct
  type t = string [@@deriving sexp_of]
end

include Abbot_other_examples.Fpcpat.Make (Label)

let add_parens_if bool string =
  match bool with
  | true -> "(" ^ string ^ ")"
  | false -> string
;;

let rec typ_to_string' ~context (typ : Typ.t) =
  match Typ.out typ with
  | Var var -> Typ.Var.name var
  | Arrow (typ1, typ2) ->
    sprintf "%s -> %s"
      (typ_to_string' ~context:`Lhs_of_arrow typ1)
      (typ_to_string' ~context:`None typ2)
    |> add_parens_if (match context with `None -> false | `Lhs_of_arrow -> true)
  | Prod fields ->
    typ_list_to_string fields
    |> sprintf "prod[%s]"
  | Sum clauses ->
    typ_list_to_string clauses
    |> sprintf "sum[%s]"
  | Rec (var, typ) -> sprintf "rec[%s.%s]" (Typ.Var.name var) (typ_to_string' ~context:`None typ)

and typ_list_to_string l =
  List.map l ~f:(fun (label, typ) ->
    sprintf "%s : %s" label (typ_to_string' ~context:`None typ))
  |> String.concat ~sep:", "
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

let rec pat_to_string' ~context (pat : Pat.t) =
  match pat with
  | Wild -> "_"
  | Var var -> Exp.Var.name var
  | Record fields -> record_to_string (pat_to_string' ~context:`None) fields
  | Inj (label, pat) ->
    sprintf "inj[%s] %s" label (pat_to_string' ~context:`Arg pat)
    |> add_parens_if (match context with `None -> false | `Arg -> true)
  | Fold pat ->
    sprintf "fold %s" (pat_to_string' ~context:`Arg pat)
    |> add_parens_if (match context with `None -> false | `Arg -> true)
  | Ascribe (pat, typ) ->
    sprintf "(%s : %s)" (pat_to_string' ~context:`None pat) (typ_to_string' ~context:`None typ)
;;

let rec exp_to_string' ~context (exp : Exp.t) =
  match Exp.out exp with
  | Var var -> Exp.Var.name var
  | Fun (arg_pat, body) ->
    sprintf "fun %s => %s"
      (pat_to_string' ~context:`None arg_pat)
      (exp_to_string' ~context:`None body)
    |> add_parens_if (match context with `None -> false | `Fun | `Arg -> true )
  | Ap (func, arg) ->
    sprintf "%s %s" (exp_to_string' ~context:`Fun func) (exp_to_string' ~context:`Arg arg)
    |> add_parens_if (match context with `None | `Fun -> false | `Arg -> true )
  | Record fields ->
    record_to_string (exp_to_string' ~context:`None) fields
  | Inj (label, exp) ->
    sprintf "inj[%s] %s" label (exp_to_string' ~context:`Arg exp)
    |> add_parens_if (match context with `None -> false | `Fun | `Arg -> true )
  | Fold exp ->
    sprintf "fold %s" (exp_to_string' ~context:`Arg exp)
    |> add_parens_if (match context with `None -> false | `Fun | `Arg -> true )
  | Match (exp, cases) ->
    (match cases with
     | [] -> sprintf "match %s with end" (exp_to_string' ~context:`None exp)
     | _::_ ->
       List.map cases ~f:(fun (pat, exp) ->
         sprintf "%s => %s" (pat_to_string' ~context:`None pat) (exp_to_string' ~context:`None exp))
       |> String.concat ~sep:" | "
       |> sprintf "match %s with %s end" (exp_to_string' ~context:`None exp))
  | Fix (var, body) ->
    sprintf "fix %s is %s" (Exp.Var.name var) (exp_to_string' ~context:`None body)
    |> add_parens_if (match context with `None -> false | `Fun | `Arg -> true )
  | Let ((pat, exp1), exp2) ->
    sprintf
      "let %s = %s in %s"
      (pat_to_string' ~context:`None pat)
      (exp_to_string' ~context:`None exp1)
      (exp_to_string' ~context:`None exp2)
    |> add_parens_if (match context with `None -> false | `Fun | `Arg -> true )
  | Let_type ((typ_var, typ), exp) ->
    sprintf
      "let type %s = %s in %s"
      (Typ.Var.name typ_var)
      (typ_to_string' ~context:`None typ)
      (exp_to_string' ~context:`None exp)
    |> add_parens_if (match context with `None -> false | `Fun | `Arg -> true )
  | Ascribe (exp, typ) ->
    sprintf "(%s : %s)" (exp_to_string' ~context:`None exp) (typ_to_string' ~context:`None typ)
;;

let typ_to_string = typ_to_string' ~context:`None
let pat_to_string = pat_to_string' ~context:`None
let exp_to_string = exp_to_string' ~context:`None
