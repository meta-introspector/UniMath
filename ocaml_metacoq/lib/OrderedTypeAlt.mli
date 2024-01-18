open Datatypes
open Specif

module type OrderedTypeAlt =
 sig
  type t

  val compare : t -> t -> comparison
 end

module OrderedType_from_Alt :
 functor (O:OrderedTypeAlt) ->
 sig
  type t = O.t

  val compare : O.t -> O.t -> O.t OrderedType.coq_Compare

  val eq_dec : O.t -> O.t -> sumbool
 end

module OrderedType_to_Alt :
 functor (O:OrderedType.OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end

  type t = O.t

  val compare : O.t -> O.t -> comparison
 end
