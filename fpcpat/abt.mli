open! Core

include Abbot_other_examples.Fpcpat_intf.S with type Label.t := string

val typ_to_string : Typ.t -> string
val pat_to_string : Pat.t -> string
val exp_to_string : Exp.t -> string
