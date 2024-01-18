open Ascii
open BinNums
open Classes
open Specif
open String

(** val ascii_eqdec : ascii coq_EqDec **)

let ascii_eqdec =
  ascii_dec

(** val string_eqdec : string coq_EqDec **)

let string_eqdec =
  string_dec

(** val coq_NoConfusionPackage_ascii : ascii coq_NoConfusionPackage **)

let coq_NoConfusionPackage_ascii =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_string : string coq_NoConfusionPackage **)

let coq_NoConfusionPackage_string =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_positive : positive coq_NoConfusionPackage **)

let coq_NoConfusionPackage_positive =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_Z : coq_Z coq_NoConfusionPackage **)

let coq_NoConfusionPackage_Z =
  Build_NoConfusionPackage

(** val positive_eqdec : positive -> positive -> positive dec_eq **)

let rec positive_eqdec p y =
  match p with
  | Coq_xI p0 ->
    (match y with
     | Coq_xI p1 -> positive_eqdec p0 p1
     | _ -> Coq_right)
  | Coq_xO p0 ->
    (match y with
     | Coq_xO p1 -> positive_eqdec p0 p1
     | _ -> Coq_right)
  | Coq_xH -> (match y with
               | Coq_xH -> Coq_left
               | _ -> Coq_right)

(** val positive_EqDec : positive coq_EqDec **)

let positive_EqDec =
  positive_eqdec

(** val coq_Z_eqdec : coq_Z -> coq_Z -> coq_Z dec_eq **)

let coq_Z_eqdec x y =
  match x with
  | Z0 -> (match y with
           | Z0 -> Coq_left
           | _ -> Coq_right)
  | Zpos p ->
    (match y with
     | Zpos p0 -> eq_dec_point p (coq_EqDec_EqDecPoint positive_EqDec p) p0
     | _ -> Coq_right)
  | Zneg p ->
    (match y with
     | Zneg p0 -> eq_dec_point p (coq_EqDec_EqDecPoint positive_EqDec p) p0
     | _ -> Coq_right)

(** val coq_Z_EqDec : coq_Z coq_EqDec **)

let coq_Z_EqDec =
  coq_Z_eqdec
