open Basics
open Datatypes
open List
open MSetInterface
open Orders
open OrdersFacts
open OrdersLists
open Specif

module Ops =
 functor (X:OrderedType) ->
 struct
  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    Coq_nil

  (** val is_empty : t -> bool **)

  let is_empty = function
  | Coq_nil -> Coq_true
  | Coq_cons (_, _) -> Coq_false

  (** val mem : X.t -> X.t list -> bool **)

  let rec mem x = function
  | Coq_nil -> Coq_false
  | Coq_cons (y, l) ->
    (match X.compare x y with
     | Eq -> Coq_true
     | Lt -> Coq_false
     | Gt -> mem x l)

  (** val add : X.t -> X.t list -> X.t list **)

  let rec add x s = match s with
  | Coq_nil -> Coq_cons (x, Coq_nil)
  | Coq_cons (y, l) ->
    (match X.compare x y with
     | Eq -> s
     | Lt -> Coq_cons (x, s)
     | Gt -> Coq_cons (y, (add x l)))

  (** val singleton : elt -> elt list **)

  let singleton x =
    Coq_cons (x, Coq_nil)

  (** val remove : X.t -> X.t list -> t **)

  let rec remove x s = match s with
  | Coq_nil -> Coq_nil
  | Coq_cons (y, l) ->
    (match X.compare x y with
     | Eq -> l
     | Lt -> s
     | Gt -> Coq_cons (y, (remove x l)))

  (** val union : t -> t -> t **)

  let rec union s = match s with
  | Coq_nil -> (fun s' -> s')
  | Coq_cons (x, l) ->
    let rec union_aux s' = match s' with
    | Coq_nil -> s
    | Coq_cons (x', l') ->
      (match X.compare x x' with
       | Eq -> Coq_cons (x, (union l l'))
       | Lt -> Coq_cons (x, (union l s'))
       | Gt -> Coq_cons (x', (union_aux l')))
    in union_aux

  (** val inter : t -> t -> t **)

  let rec inter = function
  | Coq_nil -> (fun _ -> Coq_nil)
  | Coq_cons (x, l) ->
    let rec inter_aux s' = match s' with
    | Coq_nil -> Coq_nil
    | Coq_cons (x', l') ->
      (match X.compare x x' with
       | Eq -> Coq_cons (x, (inter l l'))
       | Lt -> inter l s'
       | Gt -> inter_aux l')
    in inter_aux

  (** val diff : t -> t -> t **)

  let rec diff s = match s with
  | Coq_nil -> (fun _ -> Coq_nil)
  | Coq_cons (x, l) ->
    let rec diff_aux s' = match s' with
    | Coq_nil -> s
    | Coq_cons (x', l') ->
      (match X.compare x x' with
       | Eq -> diff l l'
       | Lt -> Coq_cons (x, (diff l s'))
       | Gt -> diff_aux l')
    in diff_aux

  (** val equal : t -> t -> bool **)

  let rec equal s s' =
    match s with
    | Coq_nil ->
      (match s' with
       | Coq_nil -> Coq_true
       | Coq_cons (_, _) -> Coq_false)
    | Coq_cons (x, l) ->
      (match s' with
       | Coq_nil -> Coq_false
       | Coq_cons (x', l') ->
         (match X.compare x x' with
          | Eq -> equal l l'
          | _ -> Coq_false))

  (** val subset : X.t list -> X.t list -> bool **)

  let rec subset s s' =
    match s with
    | Coq_nil -> Coq_true
    | Coq_cons (x, l) ->
      (match s' with
       | Coq_nil -> Coq_false
       | Coq_cons (x', l') ->
         (match X.compare x x' with
          | Eq -> subset l l'
          | Lt -> Coq_false
          | Gt -> subset s l'))

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s i =
    fold_left (flip f) s i

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | Coq_nil -> Coq_nil
  | Coq_cons (x, l) ->
    (match f x with
     | Coq_true -> Coq_cons (x, (filter f l))
     | Coq_false -> filter f l)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | Coq_nil -> Coq_true
  | Coq_cons (x, l) ->
    (match f x with
     | Coq_true -> for_all f l
     | Coq_false -> Coq_false)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | Coq_nil -> Coq_false
  | Coq_cons (x, l) ->
    (match f x with
     | Coq_true -> Coq_true
     | Coq_false -> exists_ f l)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let rec partition f = function
  | Coq_nil -> Coq_pair (Coq_nil, Coq_nil)
  | Coq_cons (x, l) ->
    let Coq_pair (s1, s2) = partition f l in
    (match f x with
     | Coq_true -> Coq_pair ((Coq_cons (x, s1)), s2)
     | Coq_false -> Coq_pair (s1, (Coq_cons (x, s2))))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements x =
    x

  (** val min_elt : t -> elt option **)

  let min_elt = function
  | Coq_nil -> None
  | Coq_cons (x, _) -> Some x

  (** val max_elt : t -> elt option **)

  let rec max_elt = function
  | Coq_nil -> None
  | Coq_cons (x, l) ->
    (match l with
     | Coq_nil -> Some x
     | Coq_cons (_, _) -> max_elt l)

  (** val choose : t -> elt option **)

  let choose =
    min_elt

  (** val compare : X.t list -> X.t list -> comparison **)

  let rec compare s s' =
    match s with
    | Coq_nil -> (match s' with
                  | Coq_nil -> Eq
                  | Coq_cons (_, _) -> Lt)
    | Coq_cons (x, s0) ->
      (match s' with
       | Coq_nil -> Gt
       | Coq_cons (x', s'0) ->
         (match X.compare x x' with
          | Eq -> compare s0 s'0
          | x0 -> x0))
 end

module MakeRaw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module ML = OrderedTypeLists(X)

  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    Coq_nil

  (** val is_empty : t -> bool **)

  let is_empty = function
  | Coq_nil -> Coq_true
  | Coq_cons (_, _) -> Coq_false

  (** val mem : X.t -> X.t list -> bool **)

  let rec mem x = function
  | Coq_nil -> Coq_false
  | Coq_cons (y, l) ->
    (match X.compare x y with
     | Eq -> Coq_true
     | Lt -> Coq_false
     | Gt -> mem x l)

  (** val add : X.t -> X.t list -> X.t list **)

  let rec add x s = match s with
  | Coq_nil -> Coq_cons (x, Coq_nil)
  | Coq_cons (y, l) ->
    (match X.compare x y with
     | Eq -> s
     | Lt -> Coq_cons (x, s)
     | Gt -> Coq_cons (y, (add x l)))

  (** val singleton : elt -> elt list **)

  let singleton x =
    Coq_cons (x, Coq_nil)

  (** val remove : X.t -> X.t list -> t **)

  let rec remove x s = match s with
  | Coq_nil -> Coq_nil
  | Coq_cons (y, l) ->
    (match X.compare x y with
     | Eq -> l
     | Lt -> s
     | Gt -> Coq_cons (y, (remove x l)))

  (** val union : t -> t -> t **)

  let rec union s = match s with
  | Coq_nil -> (fun s' -> s')
  | Coq_cons (x, l) ->
    let rec union_aux s' = match s' with
    | Coq_nil -> s
    | Coq_cons (x', l') ->
      (match X.compare x x' with
       | Eq -> Coq_cons (x, (union l l'))
       | Lt -> Coq_cons (x, (union l s'))
       | Gt -> Coq_cons (x', (union_aux l')))
    in union_aux

  (** val inter : t -> t -> t **)

  let rec inter = function
  | Coq_nil -> (fun _ -> Coq_nil)
  | Coq_cons (x, l) ->
    let rec inter_aux s' = match s' with
    | Coq_nil -> Coq_nil
    | Coq_cons (x', l') ->
      (match X.compare x x' with
       | Eq -> Coq_cons (x, (inter l l'))
       | Lt -> inter l s'
       | Gt -> inter_aux l')
    in inter_aux

  (** val diff : t -> t -> t **)

  let rec diff s = match s with
  | Coq_nil -> (fun _ -> Coq_nil)
  | Coq_cons (x, l) ->
    let rec diff_aux s' = match s' with
    | Coq_nil -> s
    | Coq_cons (x', l') ->
      (match X.compare x x' with
       | Eq -> diff l l'
       | Lt -> Coq_cons (x, (diff l s'))
       | Gt -> diff_aux l')
    in diff_aux

  (** val equal : t -> t -> bool **)

  let rec equal s s' =
    match s with
    | Coq_nil ->
      (match s' with
       | Coq_nil -> Coq_true
       | Coq_cons (_, _) -> Coq_false)
    | Coq_cons (x, l) ->
      (match s' with
       | Coq_nil -> Coq_false
       | Coq_cons (x', l') ->
         (match X.compare x x' with
          | Eq -> equal l l'
          | _ -> Coq_false))

  (** val subset : X.t list -> X.t list -> bool **)

  let rec subset s s' =
    match s with
    | Coq_nil -> Coq_true
    | Coq_cons (x, l) ->
      (match s' with
       | Coq_nil -> Coq_false
       | Coq_cons (x', l') ->
         (match X.compare x x' with
          | Eq -> subset l l'
          | Lt -> Coq_false
          | Gt -> subset s l'))

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s i =
    fold_left (flip f) s i

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | Coq_nil -> Coq_nil
  | Coq_cons (x, l) ->
    (match f x with
     | Coq_true -> Coq_cons (x, (filter f l))
     | Coq_false -> filter f l)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | Coq_nil -> Coq_true
  | Coq_cons (x, l) ->
    (match f x with
     | Coq_true -> for_all f l
     | Coq_false -> Coq_false)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | Coq_nil -> Coq_false
  | Coq_cons (x, l) ->
    (match f x with
     | Coq_true -> Coq_true
     | Coq_false -> exists_ f l)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let rec partition f = function
  | Coq_nil -> Coq_pair (Coq_nil, Coq_nil)
  | Coq_cons (x, l) ->
    let Coq_pair (s1, s2) = partition f l in
    (match f x with
     | Coq_true -> Coq_pair ((Coq_cons (x, s1)), s2)
     | Coq_false -> Coq_pair (s1, (Coq_cons (x, s2))))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements x =
    x

  (** val min_elt : t -> elt option **)

  let min_elt = function
  | Coq_nil -> None
  | Coq_cons (x, _) -> Some x

  (** val max_elt : t -> elt option **)

  let rec max_elt = function
  | Coq_nil -> None
  | Coq_cons (x, l) ->
    (match l with
     | Coq_nil -> Some x
     | Coq_cons (_, _) -> max_elt l)

  (** val choose : t -> elt option **)

  let choose =
    min_elt

  (** val compare : X.t list -> X.t list -> comparison **)

  let rec compare s s' =
    match s with
    | Coq_nil -> (match s' with
                  | Coq_nil -> Eq
                  | Coq_cons (_, _) -> Lt)
    | Coq_cons (x, s0) ->
      (match s' with
       | Coq_nil -> Gt
       | Coq_cons (x', s'0) ->
         (match X.compare x x' with
          | Eq -> compare s0 s'0
          | x0 -> x0))

  (** val inf : X.t -> X.t list -> bool **)

  let inf x = function
  | Coq_nil -> Coq_true
  | Coq_cons (y, _) ->
    (match X.compare x y with
     | Lt -> Coq_true
     | _ -> Coq_false)

  (** val isok : X.t list -> bool **)

  let rec isok = function
  | Coq_nil -> Coq_true
  | Coq_cons (x, l0) ->
    (match inf x l0 with
     | Coq_true -> isok l0
     | Coq_false -> Coq_false)

  module L = MakeListOrdering(X)
 end

module Make =
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f s =
    let p = Raw.partition f (this s) in Coq_pair ((fst p), (snd p))

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in
    (match b with
     | Coq_true -> Coq_left
     | Coq_false -> Coq_right)

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end

module type OrderedTypeWithLeibniz =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type SWithLeibniz =
 sig
  module E :
   OrderedTypeWithLeibniz

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

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module MakeWithLeibniz =
 functor (X:OrderedTypeWithLeibniz) ->
 struct
  module E = X

  module Raw = MakeRaw(X)

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f s =
    let p = Raw.partition f (this s) in Coq_pair ((fst p), (snd p))

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in
    (match b with
     | Coq_true -> Coq_left
     | Coq_false -> Coq_right)

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end
