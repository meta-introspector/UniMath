open Datatypes
open Specif

type __ = Obj.t

val sumbool_of_bool : bool -> sumbool

val bool_eq_rec : bool -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val sumbool_and : sumbool -> sumbool -> sumbool

val sumbool_or : sumbool -> sumbool -> sumbool

val sumbool_not : sumbool -> sumbool

val bool_of_sumbool : sumbool -> bool
