open HLevels
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

type __ = Obj.t

val maponpaths_1 : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths

val maponpaths_2 :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 paths

val maponpaths_12 :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths
  -> 'a3 paths

val maponpaths_3 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a4
  paths

val maponpaths_123 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2
  paths -> 'a3 -> 'a3 -> 'a3 paths -> 'a4 paths

val maponpaths_13 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3
  -> 'a3 paths -> 'a4 paths

val maponpaths_4 :
  ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3
  -> 'a4 -> 'a5 paths

val maponpaths_1234 :
  ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2
  -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths -> 'a4 -> 'a4 -> 'a4 paths -> 'a5
  paths

val maponpaths_for_constant_function :
  'a2 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths paths

val base_paths_pair_path_in2 :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a1 paths paths

val transportf_transpose_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportb_transpose_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportf_transpose_left :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportb_transpose_left :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportf_pathsinv0 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportf_comp_lemma :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths ->
  'a2 paths

val transportf_comp_lemma_hset :
  'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a1 isaset -> 'a2 paths -> 'a2 paths

val transportf_bind :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths ->
  'a2 paths

val pathscomp0_dep :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2
  paths -> 'a2 paths -> 'a2 paths

val transportf_set : 'a1 -> 'a1 paths -> 'a2 -> 'a1 isaset -> 'a2 paths

val transportf_pair :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a3 -> 'a3 paths

val weqhomot :
  ('a1 -> 'a2) -> ('a1, 'a2) weq -> ('a1, 'a2) homot -> ('a1, 'a2) isweq

val invmap_eq : ('a1, 'a2) weq -> 'a2 -> 'a1 -> 'a2 paths -> 'a1 paths

val pr1_transportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) total2 -> 'a2 paths

val pr2_transportf :
  'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) dirprod -> 'a3 paths

val coprodcomm_coprodcomm : ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths

val sumofmaps_funcomp :
  ('a1 -> 'a2) -> ('a2 -> 'a5) -> ('a3 -> 'a4) -> ('a4 -> 'a5) -> (('a1, 'a3)
  coprod, 'a5) homot

val sumofmaps_homot :
  ('a1 -> 'a3) -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3)
  homot -> ('a2, 'a3) homot -> (('a1, 'a2) coprod, 'a3) homot

val coprod_rect_compute_1 : ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a1 -> 'a3 paths

val coprod_rect_compute_2 : ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a2 -> 'a3 paths

val flipsec : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

val isweq_flipsec : ('a1 -> 'a2 -> 'a3, 'a2 -> 'a1 -> 'a3) isweq

(* val flipsec_weq : ('a1 -> 'a2 -> 'a3, 'a2 -> 'a1 -> 'a3) weq *)

val empty_hlevel : nat -> empty isofhlevel

val empty_HLevel : nat -> coq_HLevel

val coq_HLevel_fun : nat -> coq_HLevel -> coq_HLevel -> coq_HLevel

val isofhlevel_hsubtype :
  nat -> 'a1 isofhlevel -> 'a1 hsubtype -> 'a1 carrier isofhlevel

val weqtotal2 :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2, 'a4)
  total2) weq

val weq_subtypes' :
  ('a1, 'a2) weq -> ('a1, 'a3) isPredicate -> ('a2, 'a4) isPredicate -> ('a1
  -> ('a3, 'a4) logeq) -> (('a1, 'a3) total2, ('a2, 'a4) total2) weq

val weq_subtypes_iff :
  ('a1, 'a2) isPredicate -> ('a1, 'a3) isPredicate -> ('a1 -> ('a2, 'a3)
  logeq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) weq

val hlevel_total2 :
  nat -> ('a1, 'a2) total2 isofhlevel -> 'a1 isofhlevel -> 'a1 -> 'a2
  isofhlevel

val path_sigma_hprop :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a2 isaprop -> (('a1, 'a2) total2
  paths, 'a1 paths) weq

type coq_PointedType = (coq_UU, __) total2

val pointedType : 'a1 -> coq_PointedType

type underlyingType = __

val basepoint : coq_PointedType -> __

val loopSpace : coq_PointedType -> coq_PointedType

val underlyingLoop : coq_PointedType -> underlyingType -> __ paths

val _UU03a9_ : coq_PointedType -> coq_PointedType

val weq_total2_prod :
  (('a2, ('a1, 'a3) dirprod) total2, ('a1, ('a2, 'a3) total2) dirprod) weq

val totalAssociativity :
  (('a1, ('a2, 'a3) total2) total2, (('a1, 'a2) total2, 'a3) total2) weq

val paths3 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a3 -> 'a1 paths -> 'a2 paths -> 'a3
  paths -> ('a1, ('a2, 'a3) dirprod) dirprod paths

val confun : 'a2 -> 'a1 -> 'a2

type 'x path_type = 'x

val path_start : 'a1 -> 'a1 -> 'a1 paths -> 'a1

val path_end : 'a1 -> 'a1 -> 'a1 paths -> 'a1

val uniqueness : 'a1 iscontr -> 'a1 -> 'a1 paths

val uniqueness' : 'a1 iscontr -> 'a1 -> 'a1 paths

val path_inverse_to_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val path_inverse_to_right' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val pathsinv0_to_right :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> 'a1 paths paths

val pathsinv0_to_right' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val pathsinv0_to_right'' :
  'a1 -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val loop_power_nat : 'a1 -> 'a1 paths -> nat -> 'a1 paths

val irrel_paths :
  ('a1 -> 'a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1
  paths paths

val path_inv_rotate_2 :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
  paths -> 'a1 paths paths -> 'a1 paths paths

val maponpaths_naturality :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 paths ->
  'a2 paths -> 'a2 paths paths -> 'a2 paths paths -> 'a2 paths paths

val maponpaths_naturality' :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 paths ->
  'a2 paths -> 'a2 paths paths -> 'a2 paths paths -> 'a2 paths paths

val pr2_of_make_hfiber :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a2 paths paths

val pr2_of_pair : 'a1 -> 'a2 -> 'a2 paths

val pr2_of_make_weq :
  ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isweq paths

val pair_path2 :
  'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a2 paths ->
  ('a1, 'a2) total2 paths

val pair_path_in2_comp1 : 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a1 paths paths

val total2_paths2_comp1 :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a1 paths paths

val total2_paths2_comp2 :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths

val from_total2 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

val inv_equality_by_case_equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths -> ('a1,
  'a2) coprod paths paths

val equality_by_case_inv_equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) equality_cases ->
  ('a1, 'a2) equality_cases paths

val equality_by_case_equiv :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> (('a1, 'a2) coprod paths, ('a1,
  'a2) equality_cases) weq

val paths_inl_inl_equiv :
  'a1 -> 'a1 -> (('a1, 'a2) coprod paths, 'a1 paths) weq

val paths_inl_inr_equiv : 'a1 -> 'a2 -> (('a1, 'a2) coprod paths, empty) weq

val paths_inr_inr_equiv :
  'a2 -> 'a2 -> (('a1, 'a2) coprod paths, 'a2 paths) weq

val paths_inr_inl_equiv : 'a1 -> 'a2 -> (('a1, 'a2) coprod paths, empty) weq

val isInjective_inl : ('a1, ('a1, 'a2) coprod) isInjective

val isInjective_inr : ('a2, ('a1, 'a2) coprod) isInjective

val homotsec_natural :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a1 -> 'a1 -> 'a1 paths
  -> 'a2 paths paths

val evalat : 'a1 -> ('a1 -> 'a2) -> 'a2

val apfun :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> 'a1 -> 'a1 -> 'a1
  paths -> 'a2 paths

val fromemptysec : empty -> 'a1

val maponpaths_idpath : ('a1 -> 'a2) -> 'a1 -> 'a2 paths paths

val cast : __ paths -> 'a1 -> 'a2

val transport_type_path : __ paths -> 'a1 -> 'a2 paths

val transport_fun_path :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2
  paths -> 'a2 paths paths -> 'a2 paths paths

val transportf_pathsinv0' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transport_idfun : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_functions :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a3) -> 'a1
  -> 'a3 paths

val transport_funapp :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 paths

val helper_A : 'a2 -> 'a2 -> ('a1 -> 'a3) -> 'a2 paths -> 'a1 -> 'a3 paths

val helper_B :
  ('a1 -> 'a2) -> 'a2 -> 'a2 -> ('a1 -> 'a2 paths) -> 'a2 paths -> 'a1 -> 'a2
  paths paths

val transport_invweq :
  ('a1 -> ('a2, 'a3) weq) -> 'a1 -> 'a1 -> 'a1 paths -> ('a3, 'a2) weq paths

val transport_invmap :
  ('a1 -> ('a2, 'a3) weq) -> 'a1 -> 'a1 -> 'a1 paths -> ('a3 -> 'a2) paths

val transportf2 : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3

val transportb2 : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3

val maponpaths_pr1_pr2 :
  ('a1, ('a2, 'a3) total2) total2 -> ('a1, ('a2, 'a3) total2) total2 -> ('a1,
  ('a2, 'a3) total2) total2 paths -> 'a2 paths

val transportb_pair :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3 -> ('a2, 'a3) total2 paths

val transportf_total2_const :
  'a2 -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> ('a2, 'a3) total2 paths

val isaprop_wma_inhab : ('a1 -> 'a1 isaprop) -> 'a1 isaprop

val isaprop_wma_inhab' : ('a1 -> 'a1 iscontr) -> 'a1 isaprop

val coq_Unnamed_thm :
  hSet -> pr1hSet -> pr1hSet -> pr1hSet paths -> pr1hSet paths -> pr1hSet
  paths paths

val coq_Unnamed_thm0 :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 isaset -> 'a1 paths paths

val funset : hSet -> hSet

val eq_equalities_between_pairs :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> ('a1,
  'a2) total2 paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2)
  total2 paths paths

val total2_reassoc_paths :
  'a1 -> 'a1 -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 -> 'a1 paths -> 'a2
  paths -> 'a3 paths -> ('a2, 'a3) total2 paths

val total2_reassoc_paths' :
  'a1 -> 'a1 -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 -> 'a1 paths -> 'a2
  paths -> 'a3 paths -> ('a2, 'a3) total2 paths

val invrot :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val invrot' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val invrot'rot :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths
  paths

val invrotrot' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths
  paths

val hornRotation_rr :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val hornRotation_lr :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val hornRotation_rl :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val hornRotation_ll :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val uniqueFiller :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> ('a1 paths, 'a1 paths paths)
  total2 iscontr

val fillerEquation :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> ('a1 paths, 'a1 paths paths) total2 paths

val isweqpathscomp0r' :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) isweq

val transportPathTotal :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) total2 paths -> 'a3 -> 'a3

val inductionOnFiller :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a1 paths -> 'a1
  paths paths -> 'a2

val transportf_paths_FlFr :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2
  paths paths

val transportf_sec_constant :
  'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a3) -> ('a2 -> 'a3) paths

val path_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> ('a1, 'a2, 'a3) hfp paths

val maponpaths_hfpg_path_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> 'a1 paths paths

val maponpaths_hfpg'_path_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> 'a2 paths paths

val path_hfp_eta :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> ('a1, 'a2, 'a3) hfp paths -> ('a1, 'a2, 'a3) hfp paths paths

val homot_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 paths -> 'a2 paths ->
  'a2 paths paths -> 'a3 paths paths -> ('a1, 'a2, 'a3) hfp paths paths

val homot_hfp_one_type :
  'a3 isofhlevel -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp ->
  ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp paths -> ('a1, 'a2, 'a3) hfp
  paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2, 'a3) hfp paths
  paths

val hfp_is_of_hlevel :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> 'a3 isofhlevel -> ('a1 -> 'a3)
  -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp isofhlevel

val hfp_HLevel :
  nat -> coq_HLevel -> coq_HLevel -> coq_HLevel -> (__ -> __) -> (__ -> __)
  -> coq_HLevel

val transportf_total2_paths_f :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a3 -> 'a3 paths

val maponpaths_pr1_pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a1 paths paths

val maponpaths_pr2_pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths

val pathsdirprod_eta :
  ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod paths ->
  ('a1, 'a2) dirprod paths paths

val paths_pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a2 paths -> 'a2
  paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2) dirprod paths
  paths

val app_fun : ('a1 -> 'a2, 'a1) dirprod -> 'a2

val app_homot :
  ('a2 -> 'a1 -> 'a3) -> ('a2 -> 'a1 -> 'a3) -> (('a2, 'a1) dirprod -> 'a3
  paths) -> 'a2 -> ('a1 -> 'a3) paths

val maponpaths_app_fun :
  ('a1 -> 'a2, 'a1) dirprod -> ('a1 -> 'a2, 'a1) dirprod -> ('a1 -> 'a2, 'a1)
  dirprod paths -> 'a2 paths paths

val dirprod_with_prop : 'a1 isaprop -> (('a1, 'a1) dirprod, 'a1) weq

val dirprod_with_prop' :
  'a1 isaprop -> (('a1, ('a2, 'a1) dirprod) dirprod, ('a2, 'a1) dirprod) weq

val issurjective_idfun : ('a1, 'a1) issurjective

val issurjective_to_contr :
  'a1 -> ('a1 -> 'a2) -> 'a2 iscontr -> ('a1, 'a2) issurjective

val issurjective_tounit : 'a1 -> ('a1, coq_unit) issurjective

val issurjective_coprodf :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) issurjective -> ('a2, 'a4)
  issurjective -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) issurjective

val issurjective_dirprodf :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) issurjective -> ('a2, 'a4)
  issurjective -> (('a1, 'a2) dirprod, ('a3, 'a4) dirprod) issurjective

val issurjective_totalfun :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> ('a2, 'a3) issurjective) -> (('a1, 'a2)
  total2, ('a1, 'a3) total2) issurjective

val issurjective_sumofmaps_1 :
  ('a2 -> 'a1) -> ('a3 -> 'a1) -> ('a2, 'a1) issurjective -> (('a2, 'a3)
  coprod, 'a1) issurjective

val issurjective_sumofmaps_2 :
  ('a2 -> 'a1) -> ('a3 -> 'a1) -> ('a3, 'a1) issurjective -> (('a2, 'a3)
  coprod, 'a1) issurjective
