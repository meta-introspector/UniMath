open Datatypes
open FloatClass
open PrimInt63

type float_comparison =
| FEq
| FLt
| FGt
| FNotComparable

type float (* AXIOM TO BE REALIZED *)

type float_wrapper =
  float
  (* singleton inductive, whose constructor was wrap_float *)

val float_wrap : float_wrapper -> float

val printer : float_wrapper -> float

val coq_parser : float -> float

module PrimFloatNotationsInternalA :
 sig
 end

val classify : float -> float_class

val abs : float -> float

val sqrt : float -> float

val opp : float -> float

val eqb : float -> float -> bool

val ltb : float -> float -> bool

val leb : float -> float -> bool

val compare : float -> float -> float_comparison

module Leibniz :
 sig
  val eqb : float -> float -> bool
 end

val mul : float -> float -> float

val add : float -> float -> float

val sub : float -> float -> float

val div : float -> float -> float

module PrimFloatNotationsInternalB :
 sig
 end

val of_uint63 : int -> float

val normfr_mantissa : float -> int

val frshiftexp : float -> (float, int) prod

val ldshiftexp : float -> int -> float

val next_up : float -> float

val next_down : float -> float

val infinity : float

val neg_infinity : float

val nan : float

val one : float

val zero : float

val neg_zero : float

val two : float

val is_nan : float -> bool

val is_zero : float -> bool

val is_infinity : float -> bool

val is_finite : float -> bool

val get_sign : float -> bool

module PrimFloatNotations :
 sig
 end
