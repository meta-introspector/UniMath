open Datatypes
open DecidableClass
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | Coq_true -> (match b2 with
                 | Coq_true -> Coq_left
                 | Coq_false -> Coq_right)
  | Coq_false -> (match b2 with
                  | Coq_true -> Coq_right
                  | Coq_false -> Coq_left)

(** val compare : bool -> bool -> comparison **)

let compare b1 b2 =
  match b1 with
  | Coq_true -> (match b2 with
                 | Coq_true -> Eq
                 | Coq_false -> Gt)
  | Coq_false -> (match b2 with
                  | Coq_true -> Lt
                  | Coq_false -> Eq)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> (match b2 with
                  | Coq_true -> Coq_false
                  | Coq_false -> Coq_true)

(** val coq_Decidable_eq_bool : bool -> bool -> coq_Decidable **)

let coq_Decidable_eq_bool =
  eqb

(** val ifb : bool -> bool -> bool -> bool **)

let ifb b1 b2 b3 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> b3

(** val orb_true_elim : bool -> bool -> sumbool **)

let orb_true_elim b1 _ =
  match b1 with
  | Coq_true -> Coq_left
  | Coq_false -> Coq_right

(** val andb_false_elim : bool -> bool -> sumbool **)

let andb_false_elim b1 _ =
  match b1 with
  | Coq_true -> Coq_right
  | Coq_false -> Coq_left

type reflect =
| ReflectT
| ReflectF

(** val reflect_rect :
    (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)

let reflect_rect f f0 _ = function
| ReflectT -> f __
| ReflectF -> f0 __

(** val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)

let reflect_rec f f0 _ = function
| ReflectT -> f __
| ReflectF -> f0 __

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| Coq_true -> ReflectT
| Coq_false -> ReflectF

(** val reflect_dec : bool -> reflect -> sumbool **)

let reflect_dec _ = function
| ReflectT -> Coq_left
| ReflectF -> Coq_right

(** val eqb_spec : bool -> bool -> reflect **)

let eqb_spec b b' =
  match b with
  | Coq_true -> (match b' with
                 | Coq_true -> ReflectT
                 | Coq_false -> ReflectF)
  | Coq_false -> (match b' with
                  | Coq_true -> ReflectF
                  | Coq_false -> ReflectT)

module BoolNotations =
 struct
 end
