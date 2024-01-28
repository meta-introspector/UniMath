open BinNums
open BinPos
open Bool
open Datatypes
open Decimal
open Hexadecimal
open Number
open Specif

type __ = Obj.t

module N :
 sig
  type t = coq_N

  val zero : coq_N

  val one : coq_N

  val two : coq_N

  val succ_double : coq_N -> coq_N

  val double : coq_N -> coq_N

  val succ : coq_N -> coq_N

  val pred : coq_N -> coq_N

  val succ_pos : coq_N -> positive

  val add : coq_N -> coq_N -> coq_N

  val sub : coq_N -> coq_N -> coq_N

  val mul : coq_N -> coq_N -> coq_N

  val compare : coq_N -> coq_N -> comparison

  val eqb : coq_N -> coq_N -> bool

  val leb : coq_N -> coq_N -> bool

  val ltb : coq_N -> coq_N -> bool

  val min : coq_N -> coq_N -> coq_N

  val max : coq_N -> coq_N -> coq_N

  val div2 : coq_N -> coq_N

  val even : coq_N -> bool

  val odd : coq_N -> bool

  val pow : coq_N -> coq_N -> coq_N

  val square : coq_N -> coq_N

  val log2 : coq_N -> coq_N

  val size : coq_N -> coq_N

  val size_nat : coq_N -> nat

  val pos_div_eucl : positive -> coq_N -> (coq_N, coq_N) prod

  val div_eucl : coq_N -> coq_N -> (coq_N, coq_N) prod

  val div : coq_N -> coq_N -> coq_N

  val modulo : coq_N -> coq_N -> coq_N

  val gcd : coq_N -> coq_N -> coq_N

  val ggcd : coq_N -> coq_N -> (coq_N, (coq_N, coq_N) prod) prod

  val sqrtrem : coq_N -> (coq_N, coq_N) prod

  val sqrt : coq_N -> coq_N

  val coq_lor : coq_N -> coq_N -> coq_N

  val coq_land : coq_N -> coq_N -> coq_N

  val ldiff : coq_N -> coq_N -> coq_N

  val coq_lxor : coq_N -> coq_N -> coq_N

  val shiftl_nat : coq_N -> nat -> coq_N

  val shiftr_nat : coq_N -> nat -> coq_N

  val shiftl : coq_N -> coq_N -> coq_N

  val shiftr : coq_N -> coq_N -> coq_N

  val testbit_nat : coq_N -> nat -> bool

  val testbit : coq_N -> coq_N -> bool

  val to_nat : coq_N -> nat

  val of_nat : nat -> coq_N

  val iter : coq_N -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val of_uint : Decimal.uint -> coq_N

  val of_hex_uint : Hexadecimal.uint -> coq_N

  val of_num_uint : uint -> coq_N

  val of_int : Decimal.signed_int -> coq_N option

  val of_hex_int : Hexadecimal.signed_int -> coq_N option

  val of_num_int : signed_int -> coq_N option

  val to_uint : coq_N -> Decimal.uint

  val to_hex_uint : coq_N -> Hexadecimal.uint

  val to_num_uint : coq_N -> uint

  val to_num_hex_uint : coq_N -> uint

  val to_int : coq_N -> Decimal.signed_int

  val to_hex_int : coq_N -> Hexadecimal.signed_int

  val to_num_int : coq_N -> signed_int

  val to_num_hex_int : coq_N -> signed_int

  val eq_dec : coq_N -> coq_N -> sumbool

  val discr : coq_N -> positive sumor

  val binary_rect :
    'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1

  val binary_rec :
    'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1

  val peano_rect : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1

  val peano_rec : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1

  val recursion : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1

  val leb_spec0 : coq_N -> coq_N -> reflect

  val ltb_spec0 : coq_N -> coq_N -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  val measure_right_induction :
    ('a1 -> coq_N) -> coq_N -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) ->
    'a1 -> 'a2

  val measure_left_induction :
    ('a1 -> coq_N) -> coq_N -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) ->
    'a1 -> 'a2

  val measure_induction :
    ('a1 -> coq_N) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
      -> (__ -> 'a1) -> 'a1

    val max_case :
      coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      'a1

    val max_dec : coq_N -> coq_N -> sumbool

    val min_case_strong :
      coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
      -> (__ -> 'a1) -> 'a1

    val min_case :
      coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
      'a1

    val min_dec : coq_N -> coq_N -> sumbool
   end

  val max_case_strong : coq_N -> coq_N -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : coq_N -> coq_N -> 'a1 -> 'a1 -> 'a1

  val max_dec : coq_N -> coq_N -> sumbool

  val min_case_strong : coq_N -> coq_N -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : coq_N -> coq_N -> 'a1 -> 'a1 -> 'a1

  val min_dec : coq_N -> coq_N -> sumbool

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : coq_N -> coq_N

  val log2_up : coq_N -> coq_N

  module Private_NZGcdProp :
   sig
   end

  module Private_NDivProp :
   sig
    module Private_NZDiv :
     sig
     end
   end

  module Div0 :
   sig
   end

  module Private_NLcmProp :
   sig
    val lcm : coq_N -> coq_N -> coq_N
   end

  val lcm : coq_N -> coq_N -> coq_N

  module Lcm0 :
   sig
   end

  val eqb_spec : coq_N -> coq_N -> reflect

  val b2n : bool -> coq_N

  val setbit : coq_N -> coq_N -> coq_N

  val clearbit : coq_N -> coq_N -> coq_N

  val ones : coq_N -> coq_N

  val lnot : coq_N -> coq_N -> coq_N
 end

val coq_N_rec_double :
  coq_N -> 'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> 'a1
