open BinInt
open BinNums
open Datatypes
open Specif

val coq_Zeven_odd_dec : coq_Z -> sumbool

val coq_Zeven_dec : coq_Z -> sumbool

val coq_Zodd_dec : coq_Z -> sumbool

val coq_Z_modulo_2 : coq_Z -> (coq_Z, coq_Z) sum

val coq_Zsplit2 : coq_Z -> (coq_Z, coq_Z) prod
