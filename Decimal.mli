open Datatypes
open Specif

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

val uint_rect :
  'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1)
  -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> uint -> 'a1

val uint_rec :
  'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1)
  -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) ->
  (uint -> 'a1 -> 'a1) -> uint -> 'a1

type signed_int =
| Pos of uint
| Neg of uint

type decimal =
| Decimal of signed_int * uint
| DecimalExp of signed_int * uint * signed_int

val uint_beq : uint -> uint -> bool

val uint_eq_dec : uint -> uint -> sumbool

val signed_int_beq : signed_int -> signed_int -> bool

val signed_int_eq_dec : signed_int -> signed_int -> sumbool

val decimal_beq : decimal -> decimal -> bool

val decimal_eq_dec : decimal -> decimal -> sumbool

val nb_digits : uint -> nat

val nzhead : uint -> uint

val unorm : uint -> uint

val norm : signed_int -> signed_int

val opp : signed_int -> signed_int

val abs : signed_int -> uint

val revapp : uint -> uint -> uint

val rev : uint -> uint

val app : uint -> uint -> uint

val app_int : signed_int -> uint -> signed_int

val nztail : uint -> (uint, nat) prod

val nztail_int : signed_int -> (signed_int, nat) prod

val del_head : nat -> uint -> uint

val del_head_int : nat -> signed_int -> uint

val del_tail : nat -> uint -> uint

val del_tail_int : nat -> signed_int -> signed_int

module Little :
 sig
  val succ : uint -> uint

  val double : uint -> uint

  val succ_double : uint -> uint
 end

val uint_of_uint : uint -> uint

val int_of_int : signed_int -> signed_int
