open BinInt
open BinNums
open Datatypes
open PrimFloat
open SpecFloat
open Uint63

val prec : coq_Z

val emax : coq_Z

val shift : coq_Z

module Z :
 sig
  val frexp : float -> (float, coq_Z) prod

  val ldexp : float -> coq_Z -> float
 end

val ulp : float -> float

val coq_Prim2SF : float -> spec_float

val coq_SF2Prim : spec_float -> float
