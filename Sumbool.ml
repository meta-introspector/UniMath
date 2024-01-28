open Datatypes
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val sumbool_of_bool : bool -> sumbool **)

let sumbool_of_bool = function
| Coq_true -> Coq_left
| Coq_false -> Coq_right

(** val bool_eq_rec : bool -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let bool_eq_rec b x x0 =
  match b with
  | Coq_true -> x __
  | Coq_false -> x0 __

(** val sumbool_and : sumbool -> sumbool -> sumbool **)

let sumbool_and h1 h2 =
  match h1 with
  | Coq_left -> h2
  | Coq_right -> Coq_right

(** val sumbool_or : sumbool -> sumbool -> sumbool **)

let sumbool_or h1 h2 =
  match h1 with
  | Coq_left -> Coq_left
  | Coq_right -> h2

(** val sumbool_not : sumbool -> sumbool **)

let sumbool_not = function
| Coq_left -> Coq_right
| Coq_right -> Coq_left

(** val bool_of_sumbool : sumbool -> bool **)

let bool_of_sumbool = function
| Coq_left -> Coq_true
| Coq_right -> Coq_false
