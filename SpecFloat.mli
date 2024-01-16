open BinInt
open BinNums
open BinPos
open Bool
open Datatypes
open FloatClass
open Zbool
open Zpower

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * coq_Z

val emin : coq_Z -> coq_Z -> coq_Z

val fexp : coq_Z -> coq_Z -> coq_Z -> coq_Z

val digits2_pos : positive -> positive

val coq_Zdigits2 : coq_Z -> coq_Z

val canonical_mantissa : coq_Z -> coq_Z -> positive -> coq_Z -> bool

val bounded : coq_Z -> coq_Z -> positive -> coq_Z -> bool

val valid_binary : coq_Z -> coq_Z -> spec_float -> bool

val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

val location_rect : 'a1 -> (comparison -> 'a1) -> location -> 'a1

val location_rec : 'a1 -> (comparison -> 'a1) -> location -> 'a1

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

val shr_m : shr_record -> coq_Z

val shr_r : shr_record -> bool

val shr_s : shr_record -> bool

val shr_1 : shr_record -> shr_record

val loc_of_shr_record : shr_record -> location

val shr_record_of_loc : coq_Z -> location -> shr_record

val shr : shr_record -> coq_Z -> coq_Z -> (shr_record, coq_Z) prod

val shr_fexp :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> (shr_record, coq_Z) prod

val round_nearest_even : coq_Z -> location -> coq_Z

val binary_round_aux :
  coq_Z -> coq_Z -> bool -> coq_Z -> coq_Z -> location -> spec_float

val shl_align : positive -> coq_Z -> coq_Z -> (positive, coq_Z) prod

val binary_round : coq_Z -> coq_Z -> bool -> positive -> coq_Z -> spec_float

val binary_normalize : coq_Z -> coq_Z -> coq_Z -> coq_Z -> bool -> spec_float

val coq_SFopp : spec_float -> spec_float

val coq_SFabs : spec_float -> spec_float

val coq_SFcompare : spec_float -> spec_float -> comparison option

val coq_SFeqb : spec_float -> spec_float -> bool

val coq_SFltb : spec_float -> spec_float -> bool

val coq_SFleb : spec_float -> spec_float -> bool

val coq_SFclassify : coq_Z -> spec_float -> float_class

val coq_SFmul : coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float

val cond_Zopp : bool -> coq_Z -> coq_Z

val coq_SFadd : coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float

val coq_SFsub : coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float

val new_location_even : coq_Z -> coq_Z -> location

val new_location_odd : coq_Z -> coq_Z -> location

val new_location : coq_Z -> coq_Z -> location

val coq_SFdiv_core_binary :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> ((coq_Z, coq_Z) prod,
  location) prod

val coq_SFdiv : coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float

val coq_SFsqrt_core_binary :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> ((coq_Z, coq_Z) prod, location) prod

val coq_SFsqrt : coq_Z -> coq_Z -> spec_float -> spec_float

val coq_SFnormfr_mantissa : coq_Z -> spec_float -> coq_N

val coq_SFldexp : coq_Z -> coq_Z -> spec_float -> coq_Z -> spec_float

val coq_SFfrexp : coq_Z -> coq_Z -> spec_float -> (spec_float, coq_Z) prod

val coq_SFone : coq_Z -> coq_Z -> spec_float

val coq_SFulp : coq_Z -> coq_Z -> spec_float -> spec_float

val coq_SFpred_pos : coq_Z -> coq_Z -> spec_float -> spec_float

val coq_SFmax_float : coq_Z -> coq_Z -> spec_float

val coq_SFsucc : coq_Z -> coq_Z -> spec_float -> spec_float

val coq_SFpred : coq_Z -> coq_Z -> spec_float -> spec_float
