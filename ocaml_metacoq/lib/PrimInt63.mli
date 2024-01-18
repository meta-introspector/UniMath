open CarryType
open Datatypes

(* type int (\* AXIOM TO BE REALIZED *\) *)

type pos_neg_int63 =
| Pos of int
| Neg of int

val id_int : int -> int

type int_wrapper =
  int
  (* singleton inductive, whose constructor was wrap_int *)

val myzero : int_wrapper 
val myone : int_wrapper 

val int_wrap : int_wrapper -> int

val printer : int_wrapper -> pos_neg_int63

val coq_parser : pos_neg_int63 -> int option

module Int63NotationsInternalA :
 sig
 end

module Uint63NotationsInternalA :
 sig
 end

val coq_lsl : int -> int -> int

val coq_lsr : int -> int -> int

val coq_land : int -> int -> int

val coq_lor : int -> int -> int

val coq_lxor : int -> int -> int

val coq_asr : int -> int -> int

val add : int -> int -> int

val sub : int -> int -> int

val mul : int -> int -> int

val mulc : int -> int -> (int, int) prod

val div : int -> int -> int

val coq_mod : int -> int -> int

val divs : int -> int -> int

val mods : int -> int -> int

val eqb : int -> int -> bool

val ltb : int -> int -> bool

val leb : int -> int -> bool

val ltsb : int -> int -> bool

val lesb : int -> int -> bool

val addc : int -> int -> int carry

val addcarryc : int -> int -> int carry

val subc : int -> int -> int carry

val subcarryc : int -> int -> int carry

val diveucl : int -> int -> (int, int) prod

val diveucl_21 : int -> int -> int -> (int, int) prod

val addmuldiv : int -> int -> int -> int

val compare : int -> int -> comparison

val compares : int -> int -> comparison

val head0 : int -> int

val tail0 : int -> int

module PrimInt63Notations :
 sig
 end
