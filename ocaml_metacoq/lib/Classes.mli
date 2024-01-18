open Datatypes
open Specif

type __ = Obj.t

type 'a coq_NoCyclePackage =
| Build_NoCyclePackage

val apply_noCycle_left : 'a1 coq_NoCyclePackage -> 'a1 -> 'a1 -> 'a2

val apply_noCycle_right : 'a1 coq_NoCyclePackage -> 'a1 -> 'a1 -> 'a2

type 'a coq_NoConfusionPackage =
| Build_NoConfusionPackage

val apply_noConfusion :
  'a1 coq_NoConfusionPackage -> 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

type 'a dec_eq = sumbool

type 'a coq_EqDec = 'a -> 'a -> sumbool

val eq_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> sumbool

type 'a coq_EqDecPoint = 'a -> sumbool

val eq_dec_point : 'a1 -> 'a1 coq_EqDecPoint -> 'a1 -> sumbool

val coq_EqDec_EqDecPoint : 'a1 coq_EqDec -> 'a1 -> 'a1 coq_EqDecPoint

val elim_impossible_call : 'a1 -> 'a2

type 'a coq_FunctionalInduction =
  __
  (* singleton inductive, whose constructor was Build_FunctionalInduction *)

type 'a fun_ind_prf_ty = __

val fun_ind_prf : 'a1 -> 'a1 coq_FunctionalInduction -> 'a1 fun_ind_prf_ty

type ('a, 'fun_elim_ty) coq_FunctionalElimination = 'fun_elim_ty

val fun_elim : 'a1 -> nat -> ('a1, 'a2) coq_FunctionalElimination -> 'a2
