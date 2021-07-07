open! Core

val eval_type_aliases : Abt.Exp.t -> Abt.Exp.t

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
end
