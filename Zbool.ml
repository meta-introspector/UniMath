open BinInt
open BinNums
open Datatypes
open Specif
open Sumbool
open ZArith_dec
open Zeven

(** val coq_Z_lt_ge_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_lt_ge_bool x y =
  bool_of_sumbool (coq_Z_lt_ge_dec x y)

(** val coq_Z_ge_lt_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_ge_lt_bool x y =
  bool_of_sumbool (coq_Z_ge_lt_dec x y)

(** val coq_Z_le_gt_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_le_gt_bool x y =
  bool_of_sumbool (coq_Z_le_gt_dec x y)

(** val coq_Z_gt_le_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_gt_le_bool x y =
  bool_of_sumbool (coq_Z_gt_le_dec x y)

(** val coq_Z_eq_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_eq_bool x y =
  bool_of_sumbool (Z.eq_dec x y)

(** val coq_Z_noteq_bool : coq_Z -> coq_Z -> bool **)

let coq_Z_noteq_bool x y =
  bool_of_sumbool (coq_Z_noteq_dec x y)

(** val coq_Zeven_odd_bool : coq_Z -> bool **)

let coq_Zeven_odd_bool x =
  bool_of_sumbool (coq_Zeven_odd_dec x)

(** val coq_Zeq_bool : coq_Z -> coq_Z -> bool **)

let coq_Zeq_bool x y =
  match Z.compare x y with
  | Eq -> Coq_true
  | _ -> Coq_false

(** val coq_Zneq_bool : coq_Z -> coq_Z -> bool **)

let coq_Zneq_bool x y =
  match Z.compare x y with
  | Eq -> Coq_false
  | _ -> Coq_true

(** val coq_Zle_bool_total : coq_Z -> coq_Z -> sumbool **)

let coq_Zle_bool_total x y =
  match Z.leb x y with
  | Coq_true -> Coq_left
  | Coq_false -> Coq_right
