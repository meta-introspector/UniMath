open BinNums
open Bool
open Byte
open Datatypes
open Specif

val eqb : byte -> byte -> bool

module ByteNotations :
 sig
 end

val byte_eq_dec : byte -> byte -> sumbool

val to_nat : byte -> nat

val of_nat : nat -> byte option

val to_N : byte -> coq_N

val of_N : coq_N -> byte option
