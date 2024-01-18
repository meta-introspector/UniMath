open Classes
open Datatypes
open EqDec

type __ = Obj.t

type 'a coq_DependentEliminationPackage =
  __
  (* singleton inductive, whose constructor was Build_DependentEliminationPackage *)

type 'a elim_type = __

val elim : 'a1 coq_DependentEliminationPackage -> 'a1 elim_type

val solution_left : 'a1 -> 'a2 -> 'a1 -> 'a2

val eq_symmetry_dep : 'a1 -> ('a1 -> __ -> 'a2) -> 'a1 -> 'a2

val solution_left_dep : 'a1 -> 'a2 -> 'a1 -> 'a2

val solution_right : 'a1 -> 'a2 -> 'a1 -> 'a2

val solution_right_dep : 'a1 -> 'a2 -> 'a1 -> 'a2

val solution_left_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

val solution_right_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

val deletion : 'a1 -> 'a2 -> 'a2

val simplification_existT1 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val simplification_sigma1 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val eq_simplification_sigma1 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val eq_simplification_sigma1_dep :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val eq_simplification_sigma1_nondep_dep :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val eq_simplification_sigma1_dep_dep :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val simplification_sigma2_uip : 'a1 -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3

val simplification_sigma2_dec_point :
  'a1 -> 'a1 coq_EqDecPoint -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3

val simplification_K_uip : 'a1 -> 'a2 -> 'a2

type ('a, 'b, 'g) opaque_ind_pack_eq_inv = 'g

val simplify_ind_pack :
  'a1 -> 'a2 -> 'a2 -> (__ -> ('a1, 'a2, 'a3) opaque_ind_pack_eq_inv) -> 'a3

val simplify_ind_pack_inv :
  'a1 -> 'a2 -> 'a3 -> ('a1, 'a2, 'a3) opaque_ind_pack_eq_inv

val simplified_ind_pack :
  'a1 -> 'a2 -> ('a1, 'a2, 'a3) opaque_ind_pack_eq_inv -> 'a3

val depelim_module : coq_unit
