open Basics
open Bool
open Datatypes
open Orders
open OrdersTac
open Specif

module type CompareFacts =
 functor (O:DecStrOrder') ->
 sig
 end

module OrderedTypeFullFacts :
 functor (O:OrderedTypeFull') ->
 sig
  module OrderTac :
   sig
    module TO :
     sig
      type t = O.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end
   end
 end

module OrderedTypeFacts :
 functor (O:OrderedType') ->
 sig
  module OrderTac :
   sig
    module OTF :
     sig
      type t = O.t

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

  val eq_dec : O.t -> O.t -> sumbool

  val lt_dec : O.t -> O.t -> sumbool

  val eqb : O.t -> O.t -> bool
 end

module OrderedTypeTest :
 functor (O:OrderedType') ->
 sig
  module MO :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = O.t

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

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end
 end

module OrderedTypeRev :
 functor (O:OrderedTypeFull) ->
 sig
  type t = O.t

  val eq_dec : O.t -> O.t -> sumbool

  val compare : O.t -> O.t -> comparison
 end

module type CompareBasedOrder =
 functor (E:EqLtLe') ->
 functor (C:sig
  val compare : E.t -> E.t -> comparison
 end) ->
 sig
 end

module type CompareBasedOrderFacts =
 functor (E:EqLtLe') ->
 functor (C:sig
  val compare : E.t -> E.t -> comparison
 end) ->
 functor (O:sig
 end) ->
 sig
 end

module type BoolOrderFacts =
 functor (E:EqLtLe') ->
 functor (C:sig
  val compare : E.t -> E.t -> comparison
 end) ->
 functor (F:sig
  val eqb : E.t -> E.t -> bool

  val ltb : E.t -> E.t -> bool

  val leb : E.t -> E.t -> bool
 end) ->
 functor (O:sig
 end) ->
 functor (S:sig
 end) ->
 sig
  val leb_spec0 : E.t -> E.t -> reflect

  val ltb_spec0 : E.t -> E.t -> reflect
 end
