open! Core

module Types = struct
  type type_var = string
  type exp_var = string
  type label = string

  module Typ = struct
    type t =
      | Var of type_var
      | Arrow of t * t
      | Prod of (label * t) list
      | Sum of (label * t) list
      | Rec of type_var * t
  end

  module Pat = struct
    type t =
      | Wild
      | Var of exp_var
      | Record of (label * t) list
      | Inj of label * t
      | Fold of t
      | Ascribe of t * Typ.t
  end

  module Exp = struct
    type t =
      | Var of exp_var
      | Fun of Pat.t * t
      | Ap of t * t
      | Record of (label * t) list
      | Inj of label * t
      | Fold of t
      | Match of t * (Pat.t * t) list
      | Fix of exp_var * t
      | Let of (Pat.t * t) * t
      | Let_type of (type_var * Typ.t) * t
      | Ascribe of t * Typ.t
  end
end

module type Parse_tree = sig
  include module type of struct include Types end
end
