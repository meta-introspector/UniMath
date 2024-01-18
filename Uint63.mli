open BinInt
open BinNums
open Bool
open CarryType
open Datatypes
open Nat
open PrimInt63
open Specif

type __ = Obj.t

val size : nat

module Uint63NotationsInternalB :
 sig
 end

val digits : int

val max_int : int

val get_digit : int -> int -> bool

val set_digit : int -> int -> bool -> int

val is_zero : int -> bool

val is_even : int -> bool

val bit : int -> int -> bool

val opp : int -> int

val oppcarry : int -> int

val succ : int -> int

val pred : int -> int

val addcarry : int -> int -> int

val subcarry : int -> int -> int

val addc_def : int -> int -> int carry

val addcarryc_def : int -> int -> int carry

val subc_def : int -> int -> int carry

val subcarryc_def : int -> int -> int carry

val diveucl_def : int -> int -> (int, int) prod

val addmuldiv_def : int -> int -> int -> int

module Uint63NotationsInternalC :
 sig
 end

val oppc : int -> int carry

val succc : int -> int carry

val predc : int -> int carry

val compare_def : int -> int -> comparison

val to_Z_rec : nat -> int -> coq_Z

val to_Z : int -> coq_Z

val of_pos_rec : nat -> positive -> int

val of_pos : positive -> int

val of_Z : coq_Z -> int

val wB : coq_Z

module Uint63NotationsInternalD :
 sig
 end

val sqrt_step : (int -> int -> int) -> int -> int -> int

val iter_sqrt : nat -> (int -> int -> int) -> int -> int -> int

val sqrt : int -> int

val high_bit : int

val sqrt2_step : (int -> int -> int -> int) -> int -> int -> int -> int

val iter2_sqrt : nat -> (int -> int -> int -> int) -> int -> int -> int -> int

val sqrt2 : int -> int -> (int, int carry) prod

val gcd_rec : nat -> int -> int -> int

val gcd : int -> int -> int

val eqs : int -> int -> sumbool

val cast : int -> int -> (__ -> __ -> __) option

val eqo : int -> int -> __ option

val eqbP : int -> int -> reflect

val ltbP : int -> int -> reflect

val lebP : int -> int -> reflect

val b2i : bool -> int

module Uint63Notations :
 sig
 end
