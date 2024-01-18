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

(** val float_wrap : float_wrapper -> float **)

let float_wrap f =
  f

(** val printer : float_wrapper -> float **)

let printer =
  float_wrap

(** val coq_parser : float -> float **)

let coq_parser x =
  x

module PrimFloatNotationsInternalA =
 struct
 end

(** val classify : float -> float_class **)

let classify =
  failwith "AXIOM TO BE REALIZED"

(** val abs : float -> float **)

let abs =
  failwith "AXIOM TO BE REALIZED"

(** val sqrt : float -> float **)

let sqrt =
  failwith "AXIOM TO BE REALIZED"

(** val opp : float -> float **)

let opp =
  failwith "AXIOM TO BE REALIZED"

(** val eqb : float -> float -> bool **)

let eqb =
  failwith "AXIOM TO BE REALIZED"

(** val ltb : float -> float -> bool **)

let ltb =
  failwith "AXIOM TO BE REALIZED"

(** val leb : float -> float -> bool **)

let leb =
  failwith "AXIOM TO BE REALIZED"

(** val compare : float -> float -> float_comparison **)

let compare =
  failwith "AXIOM TO BE REALIZED"

module Leibniz =
 struct
  (** val eqb : float -> float -> bool **)

  let eqb =
    failwith "AXIOM TO BE REALIZED"
 end

(** val mul : float -> float -> float **)

let mul =
  failwith "AXIOM TO BE REALIZED"

(** val add : float -> float -> float **)

let add =
  failwith "AXIOM TO BE REALIZED"

(** val sub : float -> float -> float **)

let sub =
  failwith "AXIOM TO BE REALIZED"

(** val div : float -> float -> float **)

let div =
  failwith "AXIOM TO BE REALIZED"

module PrimFloatNotationsInternalB =
 struct
 end

(** val of_uint63 : int -> float **)

let of_uint63 =
  failwith "AXIOM TO BE REALIZED"

(** val normfr_mantissa : float -> int **)

let normfr_mantissa =
  failwith "AXIOM TO BE REALIZED"

(** val frshiftexp : float -> (float, int) prod **)

let frshiftexp =
  failwith "AXIOM TO BE REALIZED"

(** val ldshiftexp : float -> int -> float **)

let ldshiftexp =
  failwith "AXIOM TO BE REALIZED"

(** val next_up : float -> float **)

let next_up =
  failwith "AXIOM TO BE REALIZED"

(** val next_down : float -> float **)

let next_down =
  failwith "AXIOM TO BE REALIZED"

(** val infinity : float **)

let infinity =
  (Float64.of_float (infinity))

(** val neg_infinity : float **)

let neg_infinity =
  (Float64.of_float (neg_infinity))

(** val nan : float **)

let nan =
  (Float64.of_float (nan))

(** val one : float **)

let one =
  (Float64.of_float (0x1p+0))

(** val zero : float **)

let zero =
  (Float64.of_float (0x0p+0))

(** val neg_zero : float **)

let neg_zero =
  (Float64.of_float (-0x0p+0))

(** val two : float **)

let two =
  (Float64.of_float (0x1p+1))

(** val is_nan : float -> bool **)

let is_nan f =
  negb (eqb f f)

(** val is_zero : float -> bool **)

let is_zero f =
  eqb f zero

(** val is_infinity : float -> bool **)

let is_infinity f =
  eqb (abs f) infinity

(** val is_finite : float -> bool **)

let is_finite x =
  negb (match is_nan x with
        | Coq_true -> Coq_true
        | Coq_false -> is_infinity x)

(** val get_sign : float -> bool **)

let get_sign f =
  let f0 = match is_zero f with
           | Coq_true -> div one f
           | Coq_false -> f in
  ltb f0 zero

module PrimFloatNotations =
 struct
 end
