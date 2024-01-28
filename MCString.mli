open BinNums
open BinPos
open Byte
open Datatypes
open Decimal
open PeanoNat
open Bytestring

val nl : String.t

val string_of_list_aux : ('a1 -> String.t) -> String.t -> 'a1 list -> String.t

val string_of_list : ('a1 -> String.t) -> 'a1 list -> String.t

val print_list : ('a1 -> String.t) -> String.t -> 'a1 list -> String.t

val parens : bool -> String.t -> String.t

val string_of_uint : uint -> String.t

val string_of_nat : nat -> String.t

val string_of_positive : positive -> String.t

val string_of_Z : coq_Z -> String.t
