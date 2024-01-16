open Datatypes
open Specif

module type OrderedTypeAlt =
 sig
  type t

  val compare : t -> t -> comparison
 end

module OrderedType_from_Alt =
 functor (O:OrderedTypeAlt) ->
 struct
  type t = O.t

  (** val compare : O.t -> O.t -> O.t OrderedType.coq_Compare **)

  let compare x y =
    match O.compare x y with
    | Eq -> OrderedType.EQ
    | Lt -> OrderedType.LT
    | Gt -> OrderedType.GT

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec x y =
    match O.compare x y with
    | Eq -> Coq_left
    | _ -> Coq_right
 end

module OrderedType_to_Alt =
 functor (O:OrderedType.OrderedType) ->
 struct
  module MO = OrderedType.OrderedTypeFacts(O)

  type t = O.t

  (** val compare : O.t -> O.t -> comparison **)

  let compare x y =
    match O.compare x y with
    | OrderedType.LT -> Lt
    | OrderedType.EQ -> Eq
    | OrderedType.GT -> Gt
 end
