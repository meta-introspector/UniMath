open BinInt
open BinNums
open Datatypes
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

module MoreInt =
 functor (I:Int) ->
 struct
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

  (** val coq_ExprI_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 ->
      'a1) -> (coq_ExprI -> 'a1 -> 'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI ->
      'a1 -> 'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1) ->
      (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1) -> (I.t -> 'a1) ->
      coq_ExprI -> 'a1 **)

  let rec coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
  | EI0 -> f
  | EI1 -> f0
  | EI2 -> f1
  | EI3 -> f2
  | EIadd (e0, e1) ->
    f3 e0 (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EIopp e0 -> f4 e0 (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0)
  | EIsub (e0, e1) ->
    f5 e0 (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EImul (e0, e1) ->
    f6 e0 (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EImax (e0, e1) ->
    f7 e0 (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EIraw t0 -> f8 t0

  (** val coq_ExprI_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 ->
      'a1) -> (coq_ExprI -> 'a1 -> 'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI ->
      'a1 -> 'a1) -> (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1) ->
      (coq_ExprI -> 'a1 -> coq_ExprI -> 'a1 -> 'a1) -> (I.t -> 'a1) ->
      coq_ExprI -> 'a1 **)

  let rec coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
  | EI0 -> f
  | EI1 -> f0
  | EI2 -> f1
  | EI3 -> f2
  | EIadd (e0, e1) ->
    f3 e0 (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EIopp e0 -> f4 e0 (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0)
  | EIsub (e0, e1) ->
    f5 e0 (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EImul (e0, e1) ->
    f6 e0 (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EImax (e0, e1) ->
    f7 e0 (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e0) e1
      (coq_ExprI_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 e1)
  | EIraw t0 -> f8 t0

  type coq_ExprZ =
  | EZadd of coq_ExprZ * coq_ExprZ
  | EZopp of coq_ExprZ
  | EZsub of coq_ExprZ * coq_ExprZ
  | EZmul of coq_ExprZ * coq_ExprZ
  | EZmax of coq_ExprZ * coq_ExprZ
  | EZofI of coq_ExprI
  | EZraw of coq_Z

  (** val coq_ExprZ_rect :
      (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 ->
      'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ ->
      'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ ->
      'a1 -> 'a1) -> (coq_ExprI -> 'a1) -> (coq_Z -> 'a1) -> coq_ExprZ -> 'a1 **)

  let rec coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 = function
  | EZadd (e0, e1) ->
    f e0 (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e1)
  | EZopp e0 -> f0 e0 (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e0)
  | EZsub (e0, e1) ->
    f1 e0 (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e1)
  | EZmul (e0, e1) ->
    f2 e0 (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e1)
  | EZmax (e0, e1) ->
    f3 e0 (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rect f f0 f1 f2 f3 f4 f5 e1)
  | EZofI e0 -> f4 e0
  | EZraw z -> f5 z

  (** val coq_ExprZ_rec :
      (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 ->
      'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ ->
      'a1 -> coq_ExprZ -> 'a1 -> 'a1) -> (coq_ExprZ -> 'a1 -> coq_ExprZ ->
      'a1 -> 'a1) -> (coq_ExprI -> 'a1) -> (coq_Z -> 'a1) -> coq_ExprZ -> 'a1 **)

  let rec coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 = function
  | EZadd (e0, e1) ->
    f e0 (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e1)
  | EZopp e0 -> f0 e0 (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e0)
  | EZsub (e0, e1) ->
    f1 e0 (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e1)
  | EZmul (e0, e1) ->
    f2 e0 (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e1)
  | EZmax (e0, e1) ->
    f3 e0 (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e0) e1
      (coq_ExprZ_rec f f0 f1 f2 f3 f4 f5 e1)
  | EZofI e0 -> f4 e0
  | EZraw z -> f5 z

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

  (** val coq_ExprP_rect :
      (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
      (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
      (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP ->
      'a1 -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1 -> 'a1) ->
      (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP -> 'a1 ->
      coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP -> 'a1 -> 'a1) -> (__ -> 'a1) ->
      coq_ExprP -> 'a1 **)

  let rec coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | EPeq (e0, e1) -> f e0 e1
  | EPlt (e0, e1) -> f0 e0 e1
  | EPle (e0, e1) -> f1 e0 e1
  | EPgt (e0, e1) -> f2 e0 e1
  | EPge (e0, e1) -> f3 e0 e1
  | EPimpl (e0, e1) ->
    f4 e0 (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPequiv (e0, e1) ->
    f5 e0 (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPand (e0, e1) ->
    f6 e0 (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPor (e0, e1) ->
    f7 e0 (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPneg e0 -> f8 e0 (coq_ExprP_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0)
  | EPraw -> f9 __

  (** val coq_ExprP_rec :
      (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
      (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprZ -> coq_ExprZ -> 'a1) ->
      (coq_ExprZ -> coq_ExprZ -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP ->
      'a1 -> 'a1) -> (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1 -> 'a1) ->
      (coq_ExprP -> 'a1 -> coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP -> 'a1 ->
      coq_ExprP -> 'a1 -> 'a1) -> (coq_ExprP -> 'a1 -> 'a1) -> (__ -> 'a1) ->
      coq_ExprP -> 'a1 **)

  let rec coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | EPeq (e0, e1) -> f e0 e1
  | EPlt (e0, e1) -> f0 e0 e1
  | EPle (e0, e1) -> f1 e0 e1
  | EPgt (e0, e1) -> f2 e0 e1
  | EPge (e0, e1) -> f3 e0 e1
  | EPimpl (e0, e1) ->
    f4 e0 (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPequiv (e0, e1) ->
    f5 e0 (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPand (e0, e1) ->
    f6 e0 (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPor (e0, e1) ->
    f7 e0 (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1)
  | EPneg e0 -> f8 e0 (coq_ExprP_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0)
  | EPraw -> f9 __

  (** val ei2i : coq_ExprI -> I.t **)

  let rec ei2i = function
  | EI0 -> I._0
  | EI1 -> I._1
  | EI2 -> I._2
  | EI3 -> I._3
  | EIadd (e1, e2) -> I.add (ei2i e1) (ei2i e2)
  | EIopp e0 -> I.opp (ei2i e0)
  | EIsub (e1, e2) -> I.sub (ei2i e1) (ei2i e2)
  | EImul (e1, e2) -> I.mul (ei2i e1) (ei2i e2)
  | EImax (e1, e2) -> I.max (ei2i e1) (ei2i e2)
  | EIraw i -> i

  (** val ez2z : coq_ExprZ -> coq_Z **)

  let rec ez2z = function
  | EZadd (e1, e2) -> Z.add (ez2z e1) (ez2z e2)
  | EZopp e0 -> Z.opp (ez2z e0)
  | EZsub (e1, e2) -> Z.sub (ez2z e1) (ez2z e2)
  | EZmul (e1, e2) -> Z.mul (ez2z e1) (ez2z e2)
  | EZmax (e1, e2) -> Z.max (ez2z e1) (ez2z e2)
  | EZofI e0 -> I.i2z (ei2i e0)
  | EZraw z -> z

  (** val norm_ei : coq_ExprI -> coq_ExprZ **)

  let rec norm_ei = function
  | EI0 -> EZraw Z0
  | EI1 -> EZraw (Zpos Coq_xH)
  | EI2 -> EZraw (Zpos (Coq_xO Coq_xH))
  | EI3 -> EZraw (Zpos (Coq_xI Coq_xH))
  | EIadd (e1, e2) -> EZadd ((norm_ei e1), (norm_ei e2))
  | EIopp e0 -> EZopp (norm_ei e0)
  | EIsub (e1, e2) -> EZsub ((norm_ei e1), (norm_ei e2))
  | EImul (e1, e2) -> EZmul ((norm_ei e1), (norm_ei e2))
  | EImax (e1, e2) -> EZmax ((norm_ei e1), (norm_ei e2))
  | EIraw i -> EZofI (EIraw i)

  (** val norm_ez : coq_ExprZ -> coq_ExprZ **)

  let rec norm_ez = function
  | EZadd (e1, e2) -> EZadd ((norm_ez e1), (norm_ez e2))
  | EZopp e0 -> EZopp (norm_ez e0)
  | EZsub (e1, e2) -> EZsub ((norm_ez e1), (norm_ez e2))
  | EZmul (e1, e2) -> EZmul ((norm_ez e1), (norm_ez e2))
  | EZmax (e1, e2) -> EZmax ((norm_ez e1), (norm_ez e2))
  | EZofI e0 -> norm_ei e0
  | EZraw z -> EZraw z

  (** val norm_ep : coq_ExprP -> coq_ExprP **)

  let rec norm_ep = function
  | EPeq (e1, e2) -> EPeq ((norm_ez e1), (norm_ez e2))
  | EPlt (e1, e2) -> EPlt ((norm_ez e1), (norm_ez e2))
  | EPle (e1, e2) -> EPle ((norm_ez e1), (norm_ez e2))
  | EPgt (e1, e2) -> EPgt ((norm_ez e1), (norm_ez e2))
  | EPge (e1, e2) -> EPge ((norm_ez e1), (norm_ez e2))
  | EPimpl (e1, e2) -> EPimpl ((norm_ep e1), (norm_ep e2))
  | EPequiv (e1, e2) -> EPequiv ((norm_ep e1), (norm_ep e2))
  | EPand (e1, e2) -> EPand ((norm_ep e1), (norm_ep e2))
  | EPor (e1, e2) -> EPor ((norm_ep e1), (norm_ep e2))
  | EPneg e0 -> EPneg (norm_ep e0)
  | EPraw -> EPraw
 end

module Z_as_Int =
 struct
  type t = coq_Z

  (** val _0 : coq_Z **)

  let _0 =
    Z0

  (** val _1 : coq_Z **)

  let _1 =
    Zpos Coq_xH

  (** val _2 : coq_Z **)

  let _2 =
    Zpos (Coq_xO Coq_xH)

  (** val _3 : coq_Z **)

  let _3 =
    Zpos (Coq_xI Coq_xH)

  (** val add : coq_Z -> coq_Z -> coq_Z **)

  let add =
    Z.add

  (** val opp : coq_Z -> coq_Z **)

  let opp =
    Z.opp

  (** val sub : coq_Z -> coq_Z -> coq_Z **)

  let sub =
    Z.sub

  (** val mul : coq_Z -> coq_Z -> coq_Z **)

  let mul =
    Z.mul

  (** val max : coq_Z -> coq_Z -> coq_Z **)

  let max =
    Z.max

  (** val eqb : coq_Z -> coq_Z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : coq_Z -> coq_Z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : coq_Z -> coq_Z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : coq_Z -> coq_Z -> sumbool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : coq_Z -> coq_Z -> sumbool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in
    (match b with
     | Coq_true -> Coq_left
     | Coq_false -> Coq_right)

  (** val ge_lt_dec : coq_Z -> coq_Z -> sumbool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in
    (match b with
     | Coq_true -> Coq_right
     | Coq_false -> Coq_left)

  (** val i2z : t -> coq_Z **)

  let i2z n =
    n
 end
