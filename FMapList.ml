open Datatypes
open List
open Specif

module Raw =
 functor (X:OrderedType.OrderedType) ->
 struct
  module MX = OrderedType.OrderedTypeFacts(X)

  module PX = OrderedType.KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t, 'elt) prod list

  (** val empty : 'a1 t **)

  let empty =
    Coq_nil

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | Coq_nil -> Coq_true
  | Coq_cons (_, _) -> Coq_false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | Coq_nil -> Coq_false
  | Coq_cons (p, l) ->
    let Coq_pair (k', _) = p in
    (match X.compare k k' with
     | OrderedType.LT -> Coq_false
     | OrderedType.EQ -> Coq_true
     | OrderedType.GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | Coq_nil -> None
  | Coq_cons (p, s') ->
    let Coq_pair (k', x) = p in
    (match X.compare k k' with
     | OrderedType.LT -> None
     | OrderedType.EQ -> Some x
     | OrderedType.GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | Coq_nil -> Coq_cons ((Coq_pair (k, x)), Coq_nil)
  | Coq_cons (p, l) ->
    let Coq_pair (k', y) = p in
    (match X.compare k k' with
     | OrderedType.LT -> Coq_cons ((Coq_pair (k, x)), s)
     | OrderedType.EQ -> Coq_cons ((Coq_pair (k, x)), l)
     | OrderedType.GT -> Coq_cons ((Coq_pair (k', y)), (add k x l)))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | Coq_nil -> Coq_nil
  | Coq_cons (p, l) ->
    let Coq_pair (k', x) = p in
    (match X.compare k k' with
     | OrderedType.LT -> s
     | OrderedType.EQ -> l
     | OrderedType.GT -> Coq_cons ((Coq_pair (k', x)), (remove k l)))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | Coq_nil -> acc
    | Coq_cons (p, m') -> let Coq_pair (k, e) = p in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp0 m m' =
    match m with
    | Coq_nil ->
      (match m' with
       | Coq_nil -> Coq_true
       | Coq_cons (_, _) -> Coq_false)
    | Coq_cons (p, l) ->
      let Coq_pair (x, e) = p in
      (match m' with
       | Coq_nil -> Coq_false
       | Coq_cons (p0, l') ->
         let Coq_pair (x', e') = p0 in
         (match X.compare x x' with
          | OrderedType.EQ ->
            (match cmp0 e e' with
             | Coq_true -> equal cmp0 l l'
             | Coq_false -> Coq_false)
          | _ -> Coq_false))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | Coq_nil -> Coq_nil
  | Coq_cons (p, m') ->
    let Coq_pair (k, e) = p in Coq_cons ((Coq_pair (k, (f e))), (map f m'))

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | Coq_nil -> Coq_nil
  | Coq_cons (p, m') ->
    let Coq_pair (k, e) = p in Coq_cons ((Coq_pair (k, (f k e))), (mapi f m'))

  (** val option_cons :
      key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list **)

  let option_cons k o l =
    match o with
    | Some e -> Coq_cons ((Coq_pair (k, e)), l)
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | Coq_nil -> Coq_nil
  | Coq_cons (p, l) ->
    let Coq_pair (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | Coq_nil -> Coq_nil
  | Coq_cons (p, l') ->
    let Coq_pair (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | Coq_nil -> map2_r f
  | Coq_cons (p, l) ->
    let Coq_pair (k, e) = p in
    let rec map2_aux m' = match m' with
    | Coq_nil -> map2_l f m
    | Coq_cons (p0, l') ->
      let Coq_pair (k', e') = p0 in
      (match X.compare k k' with
       | OrderedType.LT -> option_cons k (f (Some e) None) (map2 f l m')
       | OrderedType.EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | OrderedType.GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t **)

  let rec combine m = match m with
  | Coq_nil -> map (fun e' -> Coq_pair (None, (Some e')))
  | Coq_cons (p, l) ->
    let Coq_pair (k, e) = p in
    let rec combine_aux m' = match m' with
    | Coq_nil -> map (fun e0 -> Coq_pair ((Some e0), None)) m
    | Coq_cons (p0, l') ->
      let Coq_pair (k', e') = p0 in
      (match X.compare k k' with
       | OrderedType.LT ->
         Coq_cons ((Coq_pair (k, (Coq_pair ((Some e), None)))),
           (combine l m'))
       | OrderedType.EQ ->
         Coq_cons ((Coq_pair (k, (Coq_pair ((Some e), (Some e'))))),
           (combine l l'))
       | OrderedType.GT ->
         Coq_cons ((Coq_pair (k', (Coq_pair (None, (Some e'))))),
           (combine_aux l')))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
      'a3) prod list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 Coq_nil

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (Coq_pair (o, o'))
    | None -> (match o' with
               | Some _ -> Some (Coq_pair (o, o'))
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Make =
 functor (X:OrderedType.OrderedType) ->
 struct
  module Raw = Raw(X)

  module E = X

  type key = E.t

  type 'elt slist =
    'elt Raw.t
    (* singleton inductive, whose constructor was Build_slist *)

  (** val this : 'a1 slist -> 'a1 Raw.t **)

  let this s =
    s

  type 'elt t = 'elt slist

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key, 'a1) prod list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    length (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp0 m m' =
    Raw.equal cmp0 (this m) (this m')
 end

module Make_ord =
 functor (X:OrderedType.OrderedType) ->
 functor (D:OrderedType.OrderedType) ->
 struct
  module Data = D

  module MapS = Make(X)

  module MD = OrderedType.OrderedTypeFacts(D)

  type t = D.t MapS.t

  (** val cmp : D.t -> D.t -> bool **)

  let cmp e e' =
    match D.compare e e' with
    | OrderedType.EQ -> Coq_true
    | _ -> Coq_false

  (** val compare :
      D.t MapS.slist -> D.t MapS.slist -> D.t MapS.slist
      OrderedType.coq_Compare **)

  let rec compare l m0 =
    match l with
    | Coq_nil ->
      (match m0 with
       | Coq_nil -> OrderedType.EQ
       | Coq_cons (_, _) -> OrderedType.LT)
    | Coq_cons (y, l0) ->
      (match m0 with
       | Coq_nil -> OrderedType.GT
       | Coq_cons (p, l1) ->
         let Coq_pair (t0, t1) = y in
         let Coq_pair (t2, t3) = p in
         let c = X.compare t0 t2 in
         (match c with
          | OrderedType.LT -> OrderedType.LT
          | OrderedType.EQ ->
            let c0 = D.compare t1 t3 in
            (match c0 with
             | OrderedType.LT -> OrderedType.LT
             | OrderedType.EQ -> compare l0 l1
             | OrderedType.GT -> OrderedType.GT)
          | OrderedType.GT -> OrderedType.GT))
 end
