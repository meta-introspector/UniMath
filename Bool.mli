open Datatypes
open DecidableClass
open Specif

type __ = Obj.t

val bool_dec : bool -> bool -> sumbool

val compare : bool -> bool -> comparison

val eqb : bool -> bool -> bool

val coq_Decidable_eq_bool : bool -> bool -> coq_Decidable

val ifb : bool -> bool -> bool -> bool

val orb_true_elim : bool -> bool -> sumbool

val andb_false_elim : bool -> bool -> sumbool

type reflect =
| ReflectT
| ReflectF

val reflect_rect : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val iff_reflect : bool -> reflect

val reflect_dec : bool -> reflect -> sumbool

val eqb_spec : bool -> bool -> reflect

module BoolNotations :
 sig
 end
