open BinInt
open BinNums
open Datatypes
open Specif
open Sumbool

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Dcompare_inf : comparison -> sumbool sumor **)

let coq_Dcompare_inf = function
| Eq -> Coq_inleft Coq_left
| Lt -> Coq_inleft Coq_right
| Gt -> Coq_inright

(** val coq_Zcompare_rect :
    coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let coq_Zcompare_rect n m h1 h2 h3 =
  let c = Z.compare n m in
  (match c with
   | Eq -> h1 __
   | Lt -> h2 __
   | Gt -> h3 __)

(** val coq_Zcompare_rec :
    coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let coq_Zcompare_rec =
  coq_Zcompare_rect

(** val coq_Z_lt_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Coq_left
  | _ -> Coq_right

(** val coq_Z_le_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_le_dec x y =
  match Z.compare x y with
  | Gt -> Coq_right
  | _ -> Coq_left

(** val coq_Z_gt_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_gt_dec x y =
  match Z.compare x y with
  | Gt -> Coq_left
  | _ -> Coq_right

(** val coq_Z_ge_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_ge_dec x y =
  match Z.compare x y with
  | Lt -> Coq_right
  | _ -> Coq_left

(** val coq_Z_lt_ge_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_lt_ge_dec =
  coq_Z_lt_dec

(** val coq_Z_lt_le_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_lt_le_dec =
  coq_Z_lt_ge_dec

(** val coq_Z_le_gt_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_le_gt_dec =
  coq_Z_le_dec

(** val coq_Z_gt_le_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_gt_le_dec =
  coq_Z_gt_dec

(** val coq_Z_ge_lt_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_ge_lt_dec =
  coq_Z_ge_dec

(** val coq_Z_le_lt_eq_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_le_lt_eq_dec x y =
  coq_Zcompare_rec x y (fun _ -> Coq_right) (fun _ -> Coq_left) (fun _ ->
    assert false (* absurd case *))

(** val coq_Zlt_cotrans : coq_Z -> coq_Z -> coq_Z -> sumbool **)

let coq_Zlt_cotrans x _ z =
  coq_Z_lt_ge_dec x z

(** val coq_Zlt_cotrans_pos : coq_Z -> coq_Z -> sumbool **)

let coq_Zlt_cotrans_pos x y =
  coq_Zlt_cotrans Z0 (Z.add x y) x

(** val coq_Zlt_cotrans_neg : coq_Z -> coq_Z -> sumbool **)

let coq_Zlt_cotrans_neg x y =
  match coq_Zlt_cotrans (Z.add x y) Z0 x with
  | Coq_left -> Coq_right
  | Coq_right -> Coq_left

(** val not_Zeq_inf : coq_Z -> coq_Z -> sumbool **)

let not_Zeq_inf x y =
  match coq_Z_lt_ge_dec x y with
  | Coq_left -> Coq_left
  | Coq_right ->
    (match coq_Z_le_lt_eq_dec y x with
     | Coq_left -> Coq_right
     | Coq_right -> assert false (* absurd case *))

(** val coq_Z_dec : coq_Z -> coq_Z -> sumbool sumor **)

let coq_Z_dec x y =
  match coq_Z_lt_ge_dec x y with
  | Coq_left -> Coq_inleft Coq_left
  | Coq_right ->
    (match coq_Z_le_lt_eq_dec y x with
     | Coq_left -> Coq_inleft Coq_right
     | Coq_right -> Coq_inright)

(** val coq_Z_dec' : coq_Z -> coq_Z -> sumbool sumor **)

let coq_Z_dec' x y =
  match Z.eq_dec x y with
  | Coq_left -> Coq_inright
  | Coq_right -> Coq_inleft (not_Zeq_inf x y)

(** val coq_Z_zerop : coq_Z -> sumbool **)

let coq_Z_zerop x =
  Z.eq_dec x Z0

(** val coq_Z_notzerop : coq_Z -> sumbool **)

let coq_Z_notzerop x =
  sumbool_not (coq_Z_zerop x)

(** val coq_Z_noteq_dec : coq_Z -> coq_Z -> sumbool **)

let coq_Z_noteq_dec x y =
  sumbool_not (Z.eq_dec x y)
