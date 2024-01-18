open Datatypes
open Orders
open Specif

type ord =
| OEQ
| OLT
| OLE

(** val ord_rect : 'a1 -> 'a1 -> 'a1 -> ord -> 'a1 **)

let ord_rect f f0 f1 = function
| OEQ -> f
| OLT -> f0
| OLE -> f1

(** val ord_rec : 'a1 -> 'a1 -> 'a1 -> ord -> 'a1 **)

let ord_rec f f0 f1 = function
| OEQ -> f
| OLT -> f0
| OLE -> f1

(** val trans_ord : ord -> ord -> ord **)

let trans_ord o o' =
  match o with
  | OEQ -> o'
  | OLT -> (match o' with
            | OEQ -> o
            | _ -> OLT)
  | OLE -> (match o' with
            | OEQ -> o
            | x -> x)

module type IsTotalOrder =
 functor (O:EqLtLe) ->
 sig
 end

module OrderFacts =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module OTF_to_OrderTac =
 functor (OTF:OrderedTypeFull) ->
 struct
  module TO = OTF_to_TotalOrder(OTF)
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      OTF.eq_dec
   end
 end
