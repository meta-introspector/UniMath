open BinInt
open BinPos
open Byte
open Classes
open Datatypes
open DecimalString
open FloatOps
open HexadecimalString
open MCString
open PrimFloat
open PrimInt63
open SpecFloat
open Specif
open Uint63
open Bytestring

type prim_tag =
| Coq_primInt
| Coq_primFloat

val coq_NoConfusionPackage_prim_tag : prim_tag coq_NoConfusionPackage

val prim_tag_eqdec : prim_tag -> prim_tag -> prim_tag dec_eq

val prim_tag_EqDec : prim_tag coq_EqDec

val string_of_prim_int : int -> String.t

val string_of_float : float -> String.t
