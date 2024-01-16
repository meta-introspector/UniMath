open Bool
open Byte
open ByteCompare
open Classes
open Datatypes
open ReflectEq

val coq_NoConfusionPackage_comparison : comparison coq_NoConfusionPackage

val eta_byte : (byte -> 'a1) -> byte -> 'a1

val coq_NoConfusionPackage_byte : byte coq_NoConfusionPackage

val reflect_equiv : bool -> reflect -> reflect

val byte_reflect_eq : byte coq_ReflectEq
