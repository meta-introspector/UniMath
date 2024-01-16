open Classes
open Datatypes
open EqDec

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a coq_DependentEliminationPackage =
  __
  (* singleton inductive, whose constructor was Build_DependentEliminationPackage *)

type 'a elim_type = __

(** val elim : 'a1 coq_DependentEliminationPackage -> 'a1 elim_type **)

let elim dependentEliminationPackage =
  dependentEliminationPackage

(** val solution_left : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_left _ p _ =
  p

(** val eq_symmetry_dep : 'a1 -> ('a1 -> __ -> 'a2) -> 'a1 -> 'a2 **)

let eq_symmetry_dep _ x x0 =
  x x0 __

(** val solution_left_dep : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_left_dep _ h _ =
  h

(** val solution_right : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_right _ p _ =
  p

(** val solution_right_dep : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_right_dep _ h _ =
  h

(** val solution_left_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let solution_left_let _ _ h =
  h __

(** val solution_right_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let solution_right_let _ _ h =
  h __

(** val deletion : 'a1 -> 'a2 -> 'a2 **)

let deletion _ x =
  x

(** val simplification_existT1 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let simplification_existT1 _ _ _ _ x =
  x __ __

(** val simplification_sigma1 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let simplification_sigma1 _ _ _ _ x =
  x __ __

(** val eq_simplification_sigma1 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_simplification_sigma1 _ _ _ _ x =
  x __ __

(** val eq_simplification_sigma1_dep :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_simplification_sigma1_dep _ _ _ _ x =
  x __ __

(** val eq_simplification_sigma1_nondep_dep :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_simplification_sigma1_nondep_dep _ _ _ _ x =
  x __ __

(** val eq_simplification_sigma1_dep_dep :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_simplification_sigma1_dep_dep _ _ _ _ x =
  x __ __

(** val simplification_sigma2_uip :
    'a1 -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3 **)

let simplification_sigma2_uip _ _ _ x =
  x __

(** val simplification_sigma2_dec_point :
    'a1 -> 'a1 coq_EqDecPoint -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3 **)

let simplification_sigma2_dec_point _ _ _ _ x =
  x __

(** val simplification_K_uip : 'a1 -> 'a2 -> 'a2 **)

let simplification_K_uip =
  coq_UIP_K

type ('a, 'b, 'g) opaque_ind_pack_eq_inv = 'g

(** val simplify_ind_pack :
    'a1 -> 'a2 -> 'a2 -> (__ -> ('a1, 'a2, 'a3) opaque_ind_pack_eq_inv) -> 'a3 **)

let simplify_ind_pack _ _ _ h =
  h __

(** val simplify_ind_pack_inv :
    'a1 -> 'a2 -> 'a3 -> ('a1, 'a2, 'a3) opaque_ind_pack_eq_inv **)

let simplify_ind_pack_inv _ _ h =
  h

(** val simplified_ind_pack :
    'a1 -> 'a2 -> ('a1, 'a2, 'a3) opaque_ind_pack_eq_inv -> 'a3 **)

let simplified_ind_pack _ _ t =
  t

(** val depelim_module : coq_unit **)

let depelim_module =
  Coq_tt
