open CRelationClasses
open Datatypes
open Relation
open Specif

val iffT_l : ('a1, 'a2) iffT -> 'a1 -> 'a2

type ('a, 'b, 'r) on_Trel = 'r

val flip_Reflexive : ('a1, 'a2) coq_Reflexive -> ('a1, 'a2) coq_Reflexive

val flip_Symmetric : ('a1, 'a2) coq_Symmetric -> ('a1, 'a2) coq_Symmetric

val flip_Transitive : ('a1, 'a2) coq_Transitive -> ('a1, 'a2) coq_Transitive

type ('a, 'r, 's) commutes =
  'a -> 'a -> 'a -> 'r -> 's -> ('a, ('s, 'r) prod) sigT

val clos_t_rt :
  'a1 -> 'a1 -> ('a1, 'a2) trans_clos -> ('a1, 'a2) clos_refl_trans

val clos_rt_monotone :
  ('a1, 'a2, 'a3) subrelation -> ('a1, ('a1, 'a2) clos_refl_trans, ('a1, 'a3)
  clos_refl_trans) subrelation

val relation_equivalence_inclusion :
  ('a1, 'a2, 'a3) subrelation -> ('a1, 'a3, 'a2) subrelation -> ('a1, 'a2,
  'a3) relation_equivalence

val clos_rt_disjunction_left :
  ('a1, ('a1, 'a2) clos_refl_trans, ('a1, ('a1, 'a2, 'a3)
  relation_disjunction) clos_refl_trans) subrelation

val clos_rt_disjunction_right :
  ('a1, ('a1, 'a3) clos_refl_trans, ('a1, ('a1, 'a2, 'a3)
  relation_disjunction) clos_refl_trans) subrelation

val clos_rt_trans : ('a1, ('a1, 'a2) clos_refl_trans) coq_Transitive

val clos_rt_refl : ('a1, ('a1, 'a2) clos_refl_trans) coq_Reflexive

val clos_refl_trans_prod_l :
  ('a1 -> 'a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a3)
  clos_refl_trans -> (('a1, 'a2) prod, 'a4) clos_refl_trans

val clos_refl_trans_prod_r :
  'a1 -> ('a2 -> 'a2 -> 'a3 -> 'a4) -> 'a2 -> 'a2 -> ('a2, 'a3)
  clos_refl_trans -> (('a1, 'a2) prod, 'a4) clos_refl_trans

val clos_rt_t_incl :
  ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2) clos_refl_trans, ('a1, 'a2)
  trans_clos) subrelation

val clos_t_rt_incl :
  ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2) trans_clos, ('a1, 'a2)
  clos_refl_trans) subrelation

val clos_t_rt_equiv :
  ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2) trans_clos, ('a1, 'a2)
  clos_refl_trans) relation_equivalence

val relation_disjunction_refl_l :
  ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2, 'a3) relation_disjunction)
  coq_Reflexive

val relation_disjunction_refl_r :
  ('a1, 'a3) coq_Reflexive -> ('a1, ('a1, 'a2, 'a3) relation_disjunction)
  coq_Reflexive

val clos_rt_trans_Symmetric :
  ('a1, 'a2) coq_Symmetric -> ('a1, ('a1, 'a2) clos_refl_trans) coq_Symmetric

type ('a, 'r) clos_sym = ('a, 'r, 'r) relation_disjunction

val clos_sym_Symmetric : ('a1, ('a1, 'a2) clos_sym) coq_Symmetric

val clos_refl_sym_trans_Symmetric :
  ('a1, ('a1, 'a2) clos_refl_sym_trans) coq_Symmetric

val clos_refl_sym_trans_Reflexive :
  ('a1, ('a1, 'a2) clos_refl_sym_trans) coq_Reflexive

val clos_refl_sym_trans_Transitive :
  ('a1, ('a1, 'a2) clos_refl_sym_trans) coq_Transitive

val relation_disjunction_Symmetric :
  ('a1, 'a2) coq_Symmetric -> ('a1, 'a3) coq_Symmetric -> ('a1, ('a1, 'a2,
  'a3) relation_disjunction) coq_Symmetric
