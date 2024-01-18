open Datatypes
open Equalities
open MSetInterface
open Specif

module WFactsOn =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> (t, t) prod

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> sumbool
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    match E.eq_dec x y with
    | Coq_left -> Coq_true
    | Coq_right -> Coq_false
 end

module WFacts =
 functor (M:WSets) ->
 WFactsOn(M.E)(M)

module Facts = WFacts
