open Notations
open PartA
open PartA0
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

(* val ishinh_irrel : 'a1 -> hProptoType -> hProptoType paths *)

(* val squash_to_hProp : *)
(*   hProp -> hProptoType -> ('a1 -> hProptoType) -> hProptoType *)

(* val hdisj_impl_1 : *)
(*   hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) -> hProptoType *)

(* val hdisj_impl_2 : *)
(*   hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) -> hProptoType *)

(* (\* val weqlogeq : hProp -> hProp -> (hProp paths, hProptoType) weq *\) *)

(* val decidable_proof_by_contradiction : *)
(*   hProp -> hProptoType decidable -> hProptoType -> hProptoType *)

(* val proof_by_contradiction : *)
(*   hProp -> hProptoType -> hProptoType -> hProptoType *)

(* val dneg_elim_to_LEM : (hProp -> hProptoType -> hProptoType) -> hProptoType *)

(* val negforall_to_existsneg : *)
(*   ('a1 -> hProp) -> hProptoType -> hProptoType -> hProptoType *)

(* val negimpl_to_conj : *)
(*   hProp -> hProp -> hProptoType -> hProptoType -> hProptoType *)

(* val hrel_set : hSet -> hSet *)

(* val isaprop_assume_it_is : ('a1 -> 'a1 isaprop) -> 'a1 isaprop *)

(* val isaproptotal2 : *)
(*   ('a1, 'a2) isPredicate -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) -> ('a1, *)
(*   'a2) total2 isaprop *)

(* val squash_rec : *)
(*   (hProptoType -> hProp) -> ('a1 -> hProptoType) -> hProptoType -> hProptoType *)

(* val logeq_if_both_true : *)
(*   hProp -> hProp -> hProptoType -> hProptoType -> hProptoType *)

(* val logeq_if_both_false : *)
(*   hProp -> hProp -> hProptoType -> hProptoType -> hProptoType *)

(* val proofirrelevance_hProp : hProp -> hProptoType isProofIrrelevant *)

(* val iscontr_hProp : hProp *)

(* val islogeqassochconj : *)
(*   hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq *)

(* val islogeqcommhconj : hProp -> hProp -> (hProptoType, hProptoType) logeq *)

(* val islogeqassochdisj : *)
(*   hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq *)

(* val islogeqhconj_absorb_hdisj : *)
(*   hProp -> hProp -> (hProptoType, hProptoType) logeq *)

(* val islogeqhdisj_absorb_hconj : *)
(*   hProp -> hProp -> (hProptoType, hProptoType) logeq *)

(* val islogeqhfalse_hdisj : hProp -> (hProptoType, hProptoType) logeq *)

(* val islogeqhhtrue_hconj : hProp -> (hProptoType, hProptoType) logeq *)

(* val isassoc_hconj : hProp -> hProp -> hProp -> hProp paths *)

(* val iscomm_hconj : hProp -> hProp -> hProp paths *)

(* val isassoc_hdisj : hProp -> hProp -> hProp -> hProp paths *)

(* val iscomm_hdisj : hProp -> hProp -> hProp paths *)

(* val hconj_absorb_hdisj : hProp -> hProp -> hProp paths *)

(* val hdisj_absorb_hconj : hProp -> hProp -> hProp paths *)

(* val hfalse_hdisj : hProp -> hProp paths *)

(* val htrue_hconj : hProp -> hProp paths *)

(* val squash_uniqueness : 'a1 -> hProptoType -> hProptoType paths *)

(* val coq_Unnamed_thm : 'a2 isaprop -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths *)

(* val factor_dep_through_squash : *)
(*   (hProptoType -> 'a2 isaprop) -> ('a1 -> 'a2) -> hProptoType -> 'a2 *)

(* val factor_through_squash_hProp : *)
(*   hProp -> ('a1 -> hProptoType) -> hProptoType -> hProptoType *)

(* val funspace_isaset : 'a2 isaset -> ('a1 -> 'a2) isaset *)

(* val squash_map_uniqueness : *)
(*   'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1, 'a2) *)
(*   homot -> (hProptoType, 'a2) homot *)

(* val squash_map_epi : *)
(*   'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1 -> 'a2) *)
(*   paths -> (hProptoType -> 'a2) paths *)

(* val uniqueExists : *)
(*   'a1 -> 'a1 -> ('a1, 'a2) total2 iscontr -> 'a2 -> 'a2 -> 'a1 paths *)

(* val isConnected : hProp *)

(* val predicateOnConnectedType : *)
(*   hProptoType -> ('a1 -> hProp) -> 'a1 -> hProptoType -> 'a1 -> hProptoType *)

(* val isBaseConnected : coq_PointedType -> hProp *)

(* val isConnected_isBaseConnected : *)
(*   coq_PointedType -> (hProptoType, hProptoType) logeq *)

(* val coq_BasePointComponent : coq_PointedType -> coq_PointedType *)

(* val basePointComponent_inclusion : *)
(*   coq_PointedType -> underlyingType -> underlyingType *)

(* val coq_BasePointComponent_isBaseConnected : coq_PointedType -> hProptoType *)

(* val coq_BasePointComponent_isincl : *)
(*   coq_PointedType -> (underlyingType, underlyingType) isincl *)

(* val coq_BasePointComponent_isweq : *)
(*   coq_PointedType -> hProptoType -> (underlyingType, underlyingType) isweq *)

(* val coq_BasePointComponent_weq : *)
(*   coq_PointedType -> hProptoType -> (underlyingType, underlyingType) weq *)

(* val baseConnectedness : coq_PointedType -> hProptoType -> hProptoType *)

(* val predicateOnBaseConnectedType : *)
(*   coq_PointedType -> hProptoType -> (underlyingType -> hProp) -> hProptoType *)
(*   -> underlyingType -> hProptoType *)

(* val predicateOnBasePointComponent : *)
(*   coq_PointedType -> (underlyingType -> hProp) -> hProptoType -> *)
(*   underlyingType -> hProptoType *)
