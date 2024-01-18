open Datatypes
open Orders
open Specif

type ord =
| OEQ
| OLT
| OLE

val ord_rect : 'a1 -> 'a1 -> 'a1 -> ord -> 'a1

val ord_rec : 'a1 -> 'a1 -> 'a1 -> ord -> 'a1

val trans_ord : ord -> ord -> ord

module type IsTotalOrder =
 functor (O:EqLtLe) ->
 sig
 end

module OrderFacts :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module OTF_to_OrderTac :
 functor (OTF:OrderedTypeFull) ->
 sig
  module TO :
   sig
    type t = OTF.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end
 end

module OT_to_OrderTac :
 functor (OT:OrderedType) ->
 sig
  module OTF :
   sig
    type t = OT.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  module TO :
   sig
    type t = OTF.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end
 end
