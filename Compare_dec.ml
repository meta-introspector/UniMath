open Datatypes
open Specif

(** val zerop : nat -> sumbool **)

let zerop = function
| O -> Coq_left
| S _ -> Coq_right

(** val lt_eq_lt_dec : nat -> nat -> sumbool sumor **)

let rec lt_eq_lt_dec n m =
  match n with
  | O -> (match m with
          | O -> Coq_inleft Coq_right
          | S _ -> Coq_inleft Coq_left)
  | S n0 -> (match m with
             | O -> Coq_inright
             | S n1 -> lt_eq_lt_dec n0 n1)

(** val gt_eq_gt_dec : nat -> nat -> sumbool sumor **)

let gt_eq_gt_dec =
  lt_eq_lt_dec

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
  | O -> Coq_left
  | S n0 -> (match m with
             | O -> Coq_right
             | S n1 -> le_lt_dec n0 n1)

(** val le_le_S_dec : nat -> nat -> sumbool **)

let le_le_S_dec =
  le_lt_dec

(** val le_ge_dec : nat -> nat -> sumbool **)

let le_ge_dec =
  le_lt_dec

(** val le_gt_dec : nat -> nat -> sumbool **)

let le_gt_dec =
  le_lt_dec

(** val le_lt_eq_dec : nat -> nat -> sumbool **)

let le_lt_eq_dec n m =
  let s = lt_eq_lt_dec n m in
  (match s with
   | Coq_inleft s0 -> s0
   | Coq_inright -> assert false (* absurd case *))

(** val le_dec : nat -> nat -> sumbool **)

let le_dec =
  le_gt_dec

(** val lt_dec : nat -> nat -> sumbool **)

let lt_dec n m =
  le_dec (S n) m

(** val gt_dec : nat -> nat -> sumbool **)

let gt_dec n m =
  lt_dec m n

(** val ge_dec : nat -> nat -> sumbool **)

let ge_dec n m =
  le_dec m n

(** val nat_compare_alt : nat -> nat -> comparison **)

let nat_compare_alt n m =
  match lt_eq_lt_dec n m with
  | Coq_inleft s -> (match s with
                     | Coq_left -> Lt
                     | Coq_right -> Eq)
  | Coq_inright -> Gt
