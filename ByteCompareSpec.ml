open Bool
open Byte
open ByteCompare
open Classes
open Datatypes
open ReflectEq

(** val coq_NoConfusionPackage_comparison :
    comparison coq_NoConfusionPackage **)

let coq_NoConfusionPackage_comparison =
  Build_NoConfusionPackage

(** val eta_byte : (byte -> 'a1) -> byte -> 'a1 **)

let eta_byte f =
  f

(** val coq_NoConfusionPackage_byte : byte coq_NoConfusionPackage **)

let coq_NoConfusionPackage_byte =
  Build_NoConfusionPackage

(** val reflect_equiv : bool -> reflect -> reflect **)

let reflect_equiv _ r =
  r

(** val byte_reflect_eq : byte coq_ReflectEq **)

let byte_reflect_eq =
  ByteCompare.eqb
