open Datatypes
open OrdersTac
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'x coq_Compare =
| LT
| EQ
| GT

(** val coq_Compare_rect :
    'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1
    coq_Compare -> 'a2 **)

let coq_Compare_rect _ _ f f0 f1 = function
| LT -> f __
| EQ -> f0 __
| GT -> f1 __

(** val coq_Compare_rec :
    'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> 'a1
    coq_Compare -> 'a2 **)

let coq_Compare_rec _ _ f f0 f1 = function
| LT -> f __
| EQ -> f0 __
| GT -> f1 __

module type MiniOrderedType =
 sig
  type t

  val compare : t -> t -> t coq_Compare
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t coq_Compare

  val eq_dec : t -> t -> sumbool
 end

module MOT_to_OT =
 functor (O:MiniOrderedType) ->
 struct
  type t = O.t

  (** val compare : t -> t -> t coq_Compare **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec x y =
    match compare x y with
    | EQ -> Coq_left
    | _ -> Coq_right
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> Coq_left
    | _ -> Coq_right

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Coq_left -> Coq_true
    | Coq_right -> Coq_false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end
