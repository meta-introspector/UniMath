open Datatypes
open Specif

val zerop : nat -> sumbool

val lt_eq_lt_dec : nat -> nat -> sumbool sumor

val gt_eq_gt_dec : nat -> nat -> sumbool sumor

val le_lt_dec : nat -> nat -> sumbool

val le_le_S_dec : nat -> nat -> sumbool

val le_ge_dec : nat -> nat -> sumbool

val le_gt_dec : nat -> nat -> sumbool

val le_lt_eq_dec : nat -> nat -> sumbool

val le_dec : nat -> nat -> sumbool

val lt_dec : nat -> nat -> sumbool

val gt_dec : nat -> nat -> sumbool

val ge_dec : nat -> nat -> sumbool

val nat_compare_alt : nat -> nat -> comparison
