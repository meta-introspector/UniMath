open Bool
open Datatypes
open DecidableClass
open Decimal
open Hexadecimal
open Number
open Specif

type __ = Obj.t

module Nat :
 sig
  type t = nat

  val zero : nat

  val one : nat

  val two : nat

  val succ : nat -> nat

  val pred : nat -> nat

  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val even : nat -> bool

  val odd : nat -> bool

  val pow : nat -> nat -> nat

  val tail_add : nat -> nat -> nat

  val tail_addmul : nat -> nat -> nat -> nat

  val tail_mul : nat -> nat -> nat

  val of_uint_acc : Decimal.uint -> nat -> nat

  val of_uint : Decimal.uint -> nat

  val of_hex_uint_acc : Hexadecimal.uint -> nat -> nat

  val of_hex_uint : Hexadecimal.uint -> nat

  val of_num_uint : uint -> nat

  val to_little_uint : nat -> Decimal.uint -> Decimal.uint

  val to_uint : nat -> Decimal.uint

  val to_little_hex_uint : nat -> Hexadecimal.uint -> Hexadecimal.uint

  val to_hex_uint : nat -> Hexadecimal.uint

  val to_num_uint : nat -> uint

  val to_num_hex_uint : nat -> uint

  val of_int : Decimal.signed_int -> nat option

  val of_hex_int : Hexadecimal.signed_int -> nat option

  val of_num_int : signed_int -> nat option

  val to_int : nat -> Decimal.signed_int

  val to_hex_int : nat -> Hexadecimal.signed_int

  val to_num_int : nat -> signed_int

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val gcd : nat -> nat -> nat

  val square : nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : nat -> nat

  val testbit : nat -> nat -> bool

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat

  val coq_lor : nat -> nat -> nat

  val ldiff : nat -> nat -> nat

  val coq_lxor : nat -> nat -> nat

  val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val coq_Decidable_eq_nat : nat -> nat -> coq_Decidable

  val coq_Decidable_le_nat : nat -> nat -> coq_Decidable

  val eq_dec : nat -> nat -> sumbool

  val leb_spec0 : nat -> nat -> reflect

  val ltb_spec0 : nat -> nat -> reflect

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
    ('a1 -> nat) -> nat -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 ->
    'a2

  val measure_left_induction :
    ('a1 -> nat) -> nat -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 ->
    'a2

  val measure_induction :
    ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> sumbool

    val min_case_strong :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : nat -> nat -> sumbool
   end

  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val max_dec : nat -> nat -> sumbool

  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val min_dec : nat -> nat -> sumbool

  module Private_Parity :
   sig
   end

  val iter_rect :
    ('a1 -> 'a1) -> 'a1 -> 'a2 -> (nat -> 'a1 -> 'a2 -> 'a2) -> nat -> 'a2

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : nat -> nat

  val log2_up : nat -> nat

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
    val lcm : nat -> nat -> nat
   end

  val lcm : nat -> nat -> nat

  module Lcm0 :
   sig
   end

  val eqb_spec : nat -> nat -> reflect

  val b2n : bool -> nat

  val setbit : nat -> nat -> nat

  val clearbit : nat -> nat -> nat

  val ones : nat -> nat

  val lnot : nat -> nat -> nat

  val coq_Even_Odd_dec : nat -> sumbool

  type coq_EvenT = nat

  type coq_OddT = nat

  val coq_EvenT_0 : coq_EvenT

  val coq_EvenT_2 : nat -> coq_EvenT -> coq_EvenT

  val coq_OddT_1 : coq_OddT

  val coq_OddT_2 : nat -> coq_OddT -> coq_OddT

  val coq_EvenT_S_OddT : nat -> coq_EvenT -> coq_OddT

  val coq_OddT_S_EvenT : nat -> coq_OddT -> coq_EvenT

  val even_EvenT : nat -> coq_EvenT

  val odd_OddT : nat -> coq_OddT

  val coq_Even_EvenT : nat -> coq_EvenT

  val coq_Odd_OddT : nat -> coq_OddT

  val coq_EvenT_OddT_dec : nat -> (coq_EvenT, coq_OddT) sum

  val coq_OddT_EvenT_rect :
    (nat -> coq_EvenT -> 'a2 -> 'a1) -> 'a2 -> (nat -> coq_OddT -> 'a1 ->
    'a2) -> nat -> coq_OddT -> 'a1

  val coq_EvenT_OddT_rect :
    (nat -> coq_EvenT -> 'a2 -> 'a1) -> 'a2 -> (nat -> coq_OddT -> 'a1 ->
    'a2) -> nat -> coq_EvenT -> 'a2
 end
