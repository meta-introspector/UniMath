open Classes
open Datatypes
open Orders
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val compare_cont : comparison -> comparison -> comparison **)

let compare_cont c d =
  match c with
  | Eq -> d
  | x -> x

(** val comparison_trans : comparison -> comparison -> comparison option **)

let comparison_trans p q =
  match p with
  | Eq -> Some q
  | Lt -> (match q with
           | Gt -> None
           | _ -> Some p)
  | Gt -> (match q with
           | Lt -> None
           | _ -> Some p)

module BoolOT =
 struct
  type t = bool

  (** val compare : bool -> bool -> comparison **)

  let compare x y =
    match x with
    | Coq_true -> (match y with
                   | Coq_true -> Eq
                   | Coq_false -> Gt)
    | Coq_false -> (match y with
                    | Coq_true -> Lt
                    | Coq_false -> Eq)

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec l1 l2 =
    match l1 with
    | Coq_true ->
      (match l2 with
       | Coq_true -> Coq_left
       | Coq_false -> Coq_right)
    | Coq_false ->
      (match l2 with
       | Coq_true -> Coq_right
       | Coq_false -> Coq_left)

  (** val eqb : t -> t -> bool **)

  let eqb l1 l2 =
    match compare l1 l2 with
    | Eq -> Coq_true
    | _ -> Coq_false
 end

module ListOrderedType =
 functor (A:UsualOrderedType) ->
 struct
  type t = A.t list

  (** val compare : t -> t -> comparison **)

  let rec compare l1 l2 =
    match l1 with
    | Coq_nil -> (match l2 with
                  | Coq_nil -> Eq
                  | Coq_cons (_, _) -> Lt)
    | Coq_cons (hd, tl) ->
      (match l2 with
       | Coq_nil -> Gt
       | Coq_cons (hd', tl') ->
         (match A.compare hd hd' with
          | Eq -> compare tl tl'
          | x -> x))

  (** val lt__sig_pack : t -> t -> (t * t) * __ **)

  let lt__sig_pack x x0 =
    (x,x0),__

  (** val lt__Signature : t -> t -> (t * t) * __ **)

  let lt__Signature =
    lt__sig_pack

  (** val eqb : t -> t -> bool **)

  let eqb l1 l2 =
    match compare l1 l2 with
    | Eq -> Coq_true
    | _ -> Coq_false

  (** val eqb_dec : t -> t -> sumbool **)

  let eqb_dec x y =
    let filtered_var = eqb x y in
    (match filtered_var with
     | Coq_true -> Coq_left
     | Coq_false -> Coq_right)

  (** val eq_dec : t coq_EqDec **)

  let eq_dec =
    eqb_dec
 end
