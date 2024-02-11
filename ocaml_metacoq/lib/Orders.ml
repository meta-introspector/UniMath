open Datatypes
open Equalities
open Specif

module type HasLt =
 functor (T:Typ) ->
 sig
 end

module type HasLe =
 functor (T:Typ) ->
 sig
 end

module type EqLt =
 sig
  type t
 end

module type EqLe =
 sig
  type t
 end

module type EqLtLe =
 sig
  type t
 end

module type LtNotation =
 functor (E:EqLt) ->
 sig
 end

module type LeNotation =
 functor (E:EqLe) ->
 sig
 end

module type LtLeNotation =
 functor (E:EqLtLe) ->
 sig
 end

module type EqLtNotation =
 functor (E:EqLt) ->
 sig
 end

module type EqLeNotation =
 functor (E:EqLe) ->
 sig
 end

module type EqLtLeNotation =
 functor (E:EqLtLe) ->
 sig
 end

module type EqLt' =
 sig
  type t
 end

module type EqLe' =
 sig
  type t
 end

module type EqLtLe' =
 sig
  type t
 end

module type IsStrOrder =
 functor (E:EqLt) ->
 sig
 end

module type LeIsLtEq =
 functor (E:EqLtLe') ->
 sig
 end

module type StrOrder =
 sig
  type t
 end

module type StrOrder' =
 sig
  type t
 end

module type HasCmp =
 functor (T:Typ) ->
 sig
  val compare : T.t -> T.t -> comparison
 end

module type CmpNotation =
 functor (T:Typ) ->
 functor (C:sig
  val compare : T.t -> T.t -> comparison
 end) ->
 sig
 end

module type CmpSpec =
 functor (E:EqLt') ->
 functor (C:sig
  val compare : E.t -> E.t -> comparison
 end) ->
 sig
 end

module type HasCompare =
 functor (E:EqLt) ->
 sig
  val compare : E.t -> E.t -> comparison
 end

module type DecStrOrder =
 sig
  type t

  val compare : t -> t -> comparison
 end

module type DecStrOrder' =
 sig
  type t

  val compare : t -> t -> comparison
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type OrderedTypeFull =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type OrderedTypeFull' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type UsualStrOrder =
 sig
  type t
 end

module type UsualDecStrOrder =
 sig
  type t

  val compare : t -> t -> comparison
 end

module type UsualOrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type UsualOrderedTypeFull =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type UsualStrOrder' =
 sig
  type t
 end

module type UsualDecStrOrder' =
 sig
  type t

  val compare : t -> t -> comparison
 end

module type UsualOrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type UsualOrderedTypeFull' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type LtIsTotal =
 functor (E:EqLt') ->
 sig
 end

module type TotalOrder =
 sig
  type t
 end

module type UsualTotalOrder =
 sig
  type t
 end

module type TotalOrder' =
 sig
  type t
 end

module type UsualTotalOrder' =
 sig
  type t
 end

module Compare2EqBool =
 functor (O:DecStrOrder') ->
 struct
  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match O.compare x y with
    | Eq -> Coq_true
    | _ -> Coq_false
 end

module DSO_to_OT =
 functor (O:DecStrOrder) ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match O.compare x y with
    | Eq -> Coq_true
    | _ -> Coq_false

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec x y =
    let b = match O.compare x y with
            | Eq -> Coq_true
            | _ -> Coq_false in
    (match b with
     | Coq_true -> Coq_left
     | Coq_false -> Coq_right)
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    O.eq_dec
 end

module OTF_LtIsTotal =
 functor (O:OrderedTypeFull') ->
 struct
 end

module OTF_to_TotalOrder =
 functor (O:OrderedTypeFull) ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    O.eq_dec
 end

module type HasLeb =
 functor (T:Typ) ->
 sig
  val leb : T.t -> T.t -> bool
 end

module type HasLtb =
 functor (T:Typ) ->
 sig
  val ltb : T.t -> T.t -> bool
 end

module type LebNotation =
 functor (T:Typ) ->
 functor (E:sig
  val leb : T.t -> T.t -> bool
 end) ->
 sig
 end

module type LtbNotation =
 functor (T:Typ) ->
 functor (E:sig
  val ltb : T.t -> T.t -> bool
 end) ->
 sig
 end

module type LebSpec =
 functor (T:Typ) ->
 functor (X:sig
 end) ->
 functor (Y:sig
  val leb : T.t -> T.t -> bool
 end) ->
 sig
 end

module type LtbSpec =
 functor (T:Typ) ->
 functor (X:sig
 end) ->
 functor (Y:sig
  val ltb : T.t -> T.t -> bool
 end) ->
 sig
 end

module type LeBool =
 sig
  type t

  val leb : t -> t -> bool
 end

module type LtBool =
 sig
  type t

  val ltb : t -> t -> bool
 end

module type LeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module type LtBool' =
 sig
  type t

  val ltb : t -> t -> bool
 end

module type LebIsTotal =
 functor (X:LeBool') ->
 sig
 end

module type TotalLeBool =
 sig
  type t

  val leb : t -> t -> bool
 end

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module type LebIsTransitive =
 functor (X:LeBool') ->
 sig
 end

module type TotalTransitiveLeBool =
 sig
  type t

  val leb : t -> t -> bool
 end

module type TotalTransitiveLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module type HasBoolOrdFuns =
 functor (T:Typ) ->
 sig
  val eqb : T.t -> T.t -> bool

  val ltb : T.t -> T.t -> bool

  val leb : T.t -> T.t -> bool
 end

module type HasBoolOrdFuns' =
 functor (T:Typ) ->
 sig
  val eqb : T.t -> T.t -> bool

  val ltb : T.t -> T.t -> bool

  val leb : T.t -> T.t -> bool
 end

module type BoolOrdSpecs =
 functor (O:EqLtLe) ->
 functor (F:sig
  val eqb : O.t -> O.t -> bool

  val ltb : O.t -> O.t -> bool

  val leb : O.t -> O.t -> bool
 end) ->
 sig
 end

module type OrderFunctions =
 functor (E:EqLtLe) ->
 sig
  val compare : E.t -> E.t -> comparison

  val eqb : E.t -> E.t -> bool

  val ltb : E.t -> E.t -> bool

  val leb : E.t -> E.t -> bool
 end

module type OrderFunctions' =
 functor (E:EqLtLe) ->
 sig
  val compare : E.t -> E.t -> comparison

  val eqb : E.t -> E.t -> bool

  val ltb : E.t -> E.t -> bool

  val leb : E.t -> E.t -> bool
 end

module OTF_to_TTLB =
 functor (O:OrderedTypeFull') ->
 struct
  (** val leb : O.t -> O.t -> bool **)

  let leb x y =
    match O.compare x y with
    | Gt -> Coq_false
    | _ -> Coq_true

  type t = O.t
 end

module TTLB_to_OTF =
 functor (O:TotalTransitiveLeBool') ->
 struct
  type t = O.t

  (** val compare : O.t -> O.t -> comparison **)

  let compare x y =
    match O.leb x y with
    | Coq_true -> (match O.leb y x with
                   | Coq_true -> Eq
                   | Coq_false -> Lt)
    | Coq_false -> Gt

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match O.leb x y with
    | Coq_true -> O.leb y x
    | Coq_false -> Coq_false

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec x y =
    let b =
      match O.leb x y with
      | Coq_true -> O.leb y x
      | Coq_false -> Coq_false
    in
    (match b with
     | Coq_true -> Coq_left
     | Coq_false -> Coq_right)
 end
