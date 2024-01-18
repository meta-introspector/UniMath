open Ascii
open BinNums
open Classes
open Specif
open String

val ascii_eqdec : ascii coq_EqDec

val string_eqdec : string coq_EqDec

val coq_NoConfusionPackage_ascii : ascii coq_NoConfusionPackage

val coq_NoConfusionPackage_string : string coq_NoConfusionPackage

val coq_NoConfusionPackage_positive : positive coq_NoConfusionPackage

val coq_NoConfusionPackage_Z : coq_Z coq_NoConfusionPackage

val positive_eqdec : positive -> positive -> positive dec_eq

val positive_EqDec : positive coq_EqDec

val coq_Z_eqdec : coq_Z -> coq_Z -> coq_Z dec_eq

val coq_Z_EqDec : coq_Z coq_EqDec
