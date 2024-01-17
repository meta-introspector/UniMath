open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open UnivalenceAxiom

type __ = Obj.t

(* val hProp_set : hSet *)

(* val isconst : hSet -> ('a1 -> pr1hSet) -> hProp *)

(* val squash_to_hSet : *)
(*   hSet -> ('a1 -> pr1hSet) -> hProptoType -> hProptoType -> pr1hSet *)

(* val isconst_2 : hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProp *)

(* val squash_to_hSet_2 : *)
(*   hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType -> *)
(*   hProptoType -> pr1hSet *)

(* val isconst_2' : hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProp *)

(* val squash_to_hSet_2' : *)
(*   hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType -> *)
(*   hProptoType -> pr1hSet *)

(* val eqset_to_path : hSet -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths *)

(* val isapropiscomprelfun : *)
(*   hSet -> 'a1 hrel -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun isaprop *)

(* val iscomprelfun_funcomp : *)
(*   'a1 hrel -> 'a2 hrel -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) *)
(*   iscomprelrelfun -> ('a2, 'a3) iscomprelfun -> ('a1, 'a3) iscomprelfun *)

(* val fun_hrel_comp : ('a1 -> 'a2) -> 'a2 hrel -> 'a1 hrel *)

(* val setquotunivprop' : *)
(*   'a1 eqrel -> ('a1 setquot -> 'a2 isaprop) -> ('a1 -> 'a2) -> 'a1 setquot -> *)
(*   'a2 *)

(* val setquotuniv2prop' : *)
(*   'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a2 isaprop) -> ('a1 -> 'a1 -> *)
(*   'a2) -> 'a1 setquot -> 'a1 setquot -> 'a2 *)

(* val setquotuniv3prop' : *)
(*   'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a2 isaprop) -> *)
(*   ('a1 -> 'a1 -> 'a1 -> 'a2) -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot -> *)
(*   'a2 *)

(* val setquotuniv4prop' : *)
(*   'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot -> *)
(*   'a2 isaprop) -> ('a1 -> 'a1 -> 'a1 -> 'a1 -> 'a2) -> 'a1 setquot -> 'a1 *)
(*   setquot -> 'a1 setquot -> 'a1 setquot -> 'a2 *)

(* val same_fiber_eqrel : hSet -> hSet -> (pr1hSet -> pr1hSet) -> pr1hSet eqrel *)

(* (\* val pi0 : hSet *\) *)

(* (\* val _UU03c0__UU2080_ : hSet *\) *)

(* (\* val component : 'a1 -> pr1hSet *\) *)

(* (\* val _UU03c0__UU2080__map : ('a1 -> 'a2) -> pr1hSet -> pr1hSet *\) *)

(* (\* val _UU03c0__UU2080__universal_property : *\) *)
(* (\*   hSet -> (pr1hSet -> pr1hSet, 'a1 -> pr1hSet) weq *\) *)

(* (\* val _UU03c0__UU2080__universal_map : *\) *)
(* (\*   hSet -> ('a1 -> pr1hSet) -> pr1hSet -> pr1hSet *\) *)

(* val _UU03c0__UU2080__universal_map_eqn : *)
(*   hSet -> ('a1 -> pr1hSet) -> 'a1 -> pr1hSet paths *)

(* (\* val _UU03c0__UU2080__universal_map_uniq : *\) *)
(* (\*   hSet -> (pr1hSet -> pr1hSet) -> (pr1hSet -> pr1hSet) -> ('a1 -> pr1hSet *\) *)
(* (\*   paths) -> (pr1hSet, pr1hSet) homot *\) *)

(* val isaprop_eqrel_from_hrel : *)
(*   'a1 hrel -> 'a1 -> 'a1 -> ('a1 eqrel -> ('a1 -> 'a1 -> hProptoType -> *)
(*   hProptoType) -> hProptoType) isaprop *)

(* val eqrel_from_hrel : 'a1 hrel -> 'a1 hrel *)

(* val iseqrel_eqrel_from_hrel : 'a1 hrel -> 'a1 iseqrel *)

(* val eqrel_impl : 'a1 hrel -> 'a1 -> 'a1 -> hProptoType -> hProptoType *)

(* val minimal_eqrel_from_hrel : *)
(*   'a1 hrel -> 'a1 eqrel -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> 'a1 *)
(*   -> 'a1 -> hProptoType -> hProptoType *)

(* val eqreleq : 'a1 eqrel -> 'a1 -> 'a1 -> 'a1 paths -> hProptoType *)

(* val isaprop_isirrefl : 'a1 hrel -> 'a1 isirrefl isaprop *)

(* val isaprop_issymm : 'a1 hrel -> 'a1 issymm isaprop *)

(* val isaprop_iscotrans : 'a1 hrel -> 'a1 iscotrans isaprop *)

(* val univalence_hSet : hSet -> hSet -> (pr1hSet, pr1hSet) weq -> hSet paths *)

(* val hSet_univalence_map_univalence_hSet : *)
(*   hSet -> hSet -> (pr1hSet, pr1hSet) weq -> (__, __) weq paths *)

(* val hSet_univalence_univalence_hSet_map : *)
(*   hSet -> hSet -> hSet paths -> hSet paths paths *)

(* val univalence_hSet_idweq : hSet -> hSet paths paths *)

(* val hSet_univalence_map_inv : hSet -> hSet -> hSet paths -> (__, __) weq paths *)

(* val univalence_hSet_inv : *)
(*   hSet -> hSet -> (pr1hSet, pr1hSet) weq -> hSet paths paths *)
