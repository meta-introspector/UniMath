open Classes
open Datatypes
open Orders
open Specif

type __ = Obj.t

val compare_cont : comparison -> comparison -> comparison

val comparison_trans : comparison -> comparison -> comparison option

module BoolOT :
 sig
  type t = bool

  val compare : bool -> bool -> comparison

  val eq_dec : t -> t -> sumbool

  val eqb : t -> t -> bool
 end

module ListOrderedType :
 functor (A:UsualOrderedType) ->
 sig
  type t = A.t list

  val compare : t -> t -> comparison

  val lt__sig_pack : t -> t -> (t * t) * __

  val lt__Signature : t -> t -> (t * t) * __

  val eqb : t -> t -> bool

  val eqb_dec : t -> t -> sumbool

  val eq_dec : t coq_EqDec
 end
