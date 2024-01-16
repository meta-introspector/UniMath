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

module OrderedTypeFullFacts =
 functor (O:OrderedTypeFull') ->
 struct
  module OrderTac = OTF_to_OrderTac(O)
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    let c = coq_CompSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> Coq_left
     | _ -> Coq_right)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Coq_left -> Coq_true
    | Coq_right -> Coq_false
 end

module OrderedTypeTest =
 functor (O:OrderedType') ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module OrderedTypeRev =
 functor (O:OrderedTypeFull) ->
 struct
  type t = O.t

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> comparison **)

  let compare =
    flip O.compare
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
