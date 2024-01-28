open BinInt
open BinNums
open Datatypes
open Specif

type __ = Obj.t

module type Int =
 sig
  type t

  val i2z : t -> coq_Z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> sumbool

  val ge_lt_dec : t -> t -> sumbool

  val eq_dec : t -> t -> sumbool
 end

module MoreInt :
 functor (I:Int) ->
 sig
  type coq_ExprI =
  | EI0
  | EI1
  | EI2
  | EI3
  | EIadd of coq_ExprI * coq_ExprI
  | EIopp of coq_ExprI
  | EIsub of coq_ExprI * coq_ExprI
  | EImul of coq_ExprI * coq_ExprI
  | EImax of coq_ExprI * coq_ExprI
  | EIraw of I.t

  val coq_ExprI_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1)
    -> (coq_ExprI -> 'a1 -> 'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 ->
    'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1) -> (coq_ExprI ->
    'a1 -> coq_ExprI -> 'a1 -> 'a1) -> (I.t -> 'a1) -> coq_ExprI -> 'a1

  val coq_ExprI_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1)
    -> (coq_ExprI -> 'a1 -> 'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 ->
    'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1) -> (coq_ExprI ->
    'a1 -> coq_ExprI -> 'a1 -> 'a1) -> (I.t -> 'a1) -> coq_ExprI -> 'a1

  type coq_ExprZ =
  | EZadd of coq_ExprZ * coq_ExprZ
  | EZopp of coq_ExprZ
  | EZsub of coq_ExprZ * coq_ExprZ
  | EZmul of coq_ExprZ * coq_ExprZ
  | EZmax of coq_ExprZ * coq_ExprZ
  | EZofI of coq_ExprI
  | EZraw of coq_Z

  val coq_ExprZ_rect :
    (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 ->
    'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ ->
    'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1
    -> 'a1) -> (coq_ExprI -> 'a1) -> (coq_Z -> 'a1) -> coq_ExprZ -> 'a1

  val coq_ExprZ_rec :
    (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 ->
    'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ ->
    'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1
    -> 'a1) -> (coq_ExprI -> 'a1) -> (coq_Z -> 'a1) -> coq_ExprZ -> 'a1

  type coq_ExprP =
  | EPeq of coq_ExprZ * coq_ExprZ
  | EPlt of coq_ExprZ * coq_ExprZ
  | EPle of coq_ExprZ * coq_ExprZ
  | EPgt of coq_ExprZ * coq_ExprZ
  | EPge of coq_ExprZ * coq_ExprZ
  | EPimpl of coq_ExprP * coq_ExprP
  | EPequiv of coq_ExprP * coq_ExprP
  | EPand of coq_ExprP * coq_ExprP
  | EPor of coq_ExprP * coq_ExprP
  | EPneg of coq_ExprP
  | EPraw

  val coq_ExprP_rect :
    (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
    (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
    (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1
    -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP ->
    'a1 -> coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1
    -> 'a1) -> (coq_ExprP -> 'a1 -> 'a1) -> (__ -> 'a1) -> coq_ExprP -> 'a1

  val coq_ExprP_rec :
    (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
    (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
    (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1
    -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP ->
    'a1 -> coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1
    -> 'a1) -> (coq_ExprP -> 'a1 -> 'a1) -> (__ -> 'a1) -> coq_ExprP -> 'a1

  val ei2i : coq_ExprI -> I.t

  val ez2z : coq_ExprZ -> coq_Z

  val norm_ei : coq_ExprI -> coq_ExprZ

  val norm_ez : coq_ExprZ -> coq_ExprZ

  val norm_ep : coq_ExprP -> coq_ExprP
 end

module Z_as_Int :
 sig
  type t = coq_Z

  val _0 : coq_Z

  val _1 : coq_Z

  val _2 : coq_Z

  val _3 : coq_Z

  val add : coq_Z -> coq_Z -> coq_Z

  val opp : coq_Z -> coq_Z

  val sub : coq_Z -> coq_Z -> coq_Z

  val mul : coq_Z -> coq_Z -> coq_Z

  val max : coq_Z -> coq_Z -> coq_Z

  val eqb : coq_Z -> coq_Z -> bool

  val ltb : coq_Z -> coq_Z -> bool

  val leb : coq_Z -> coq_Z -> bool

  val eq_dec : coq_Z -> coq_Z -> sumbool

  val gt_le_dec : coq_Z -> coq_Z -> sumbool

  val ge_lt_dec : coq_Z -> coq_Z -> sumbool

  val i2z : t -> coq_Z
 end
