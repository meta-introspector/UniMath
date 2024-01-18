open BinInt
open BinNums
open Datatypes
open Specif

(** val coq_Zeven_odd_dec : coq_Z -> sumbool **)

let coq_Zeven_odd_dec = function
| Z0 -> Coq_left
| Zpos p -> (match p with
             | Coq_xO _ -> Coq_left
             | _ -> Coq_right)
| Zneg p -> (match p with
             | Coq_xO _ -> Coq_left
             | _ -> Coq_right)

(** val coq_Zeven_dec : coq_Z -> sumbool **)

let coq_Zeven_dec = function
| Z0 -> Coq_left
| Zpos p -> (match p with
             | Coq_xO _ -> Coq_left
             | _ -> Coq_right)
| Zneg p -> (match p with
             | Coq_xO _ -> Coq_left
             | _ -> Coq_right)

(** val coq_Zodd_dec : coq_Z -> sumbool **)

let coq_Zodd_dec = function
| Z0 -> Coq_right
| Zpos p -> (match p with
             | Coq_xO _ -> Coq_right
             | _ -> Coq_left)
| Zneg p -> (match p with
             | Coq_xO _ -> Coq_right
             | _ -> Coq_left)

(** val coq_Z_modulo_2 : coq_Z -> (coq_Z, coq_Z) sum **)

let coq_Z_modulo_2 n =
  let s = coq_Zeven_odd_dec n in
  (match s with
   | Coq_left -> Coq_inl (Z.div2 n)
   | Coq_right -> Coq_inr (Z.div2 n))

(** val coq_Zsplit2 : coq_Z -> (coq_Z, coq_Z) prod **)

let coq_Zsplit2 n =
  let s = coq_Z_modulo_2 n in
  (match s with
   | Coq_inl s0 -> Coq_pair (s0, s0)
   | Coq_inr s0 -> Coq_pair (s0, (Z.add s0 (Zpos Coq_xH))))
