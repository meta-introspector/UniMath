open Bool
open CRelationClasses
open Classes
open Compare_dec
open Datatypes
open EqdepFacts
open List
open MCList
open MCOption
open MCReflect
open MCRelations
open Nat
open Signature
open Specif

type __ = Obj.t

val coq_Forall_sig_pack : 'a1 list -> 'a1 list * __

val coq_Forall_Signature : 'a1 list -> 'a1 list * __

val coq_Forall2_sig_pack : 'a1 list -> 'a2 list -> ('a1 list * 'a2 list) * __

val coq_Forall2_Signature : 'a1 list -> 'a2 list -> ('a1 list * 'a2 list) * __

type ('a, 'p) coq_All =
| All_nil
| All_cons of 'a * 'a list * 'p * ('a, 'p) coq_All

val coq_All_rect :
  'a3 -> ('a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_All -> 'a3 -> 'a3) -> 'a1
  list -> ('a1, 'a2) coq_All -> 'a3

val coq_All_rec :
  'a3 -> ('a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_All -> 'a3 -> 'a3) -> 'a1
  list -> ('a1, 'a2) coq_All -> 'a3

type ('a, 'p) coq_All_sig = ('a, 'p) coq_All

val coq_All_sig_pack :
  'a1 list -> ('a1, 'a2) coq_All -> 'a1 list * ('a1, 'a2) coq_All

val coq_All_Signature :
  'a1 list -> (('a1, 'a2) coq_All, 'a1 list, ('a1, 'a2) coq_All_sig)
  coq_Signature

val coq_NoConfusionPackage_All :
  ('a1 list * ('a1, 'a2) coq_All) coq_NoConfusionPackage

type ('a, 'p) coq_Alli =
| Alli_nil
| Alli_cons of 'a * 'a list * 'p * ('a, 'p) coq_Alli

val coq_Alli_rect :
  (nat -> 'a3) -> (nat -> 'a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_Alli ->
  'a3 -> 'a3) -> nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> 'a3

val coq_Alli_rec :
  (nat -> 'a3) -> (nat -> 'a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_Alli ->
  'a3 -> 'a3) -> nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> 'a3

type ('a, 'p) coq_Alli_sig = ('a, 'p) coq_Alli

val coq_Alli_sig_pack :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> (nat * 'a1 list) * ('a1, 'a2)
  coq_Alli

val coq_Alli_Signature :
  nat -> 'a1 list -> (('a1, 'a2) coq_Alli, nat * 'a1 list, ('a1, 'a2)
  coq_Alli_sig) coq_Signature

val coq_NoConfusionHomPackage_Alli :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli coq_NoConfusionPackage

type ('a, 'b, 'r) coq_All2 =
| All2_nil
| All2_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2

val coq_All2_rect :
  'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
  coq_All2 -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2
  -> 'a4

val coq_All2_rec :
  'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
  coq_All2 -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2
  -> 'a4

type ('a, 'b, 'r) coq_All2_sig = ('a, 'b, 'r) coq_All2

val coq_All2_sig_pack :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 list * 'a2
  list) * ('a1, 'a2, 'a3) coq_All2

val coq_All2_Signature :
  'a1 list -> 'a2 list -> (('a1, 'a2, 'a3) coq_All2, 'a1 list * 'a2 list,
  ('a1, 'a2, 'a3) coq_All2_sig) coq_Signature

val coq_NoConfusionHomPackage_All2 :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 coq_NoConfusionPackage

type ('a, 'b, 'r, 'x) coq_All2_dep =
| All2_dep_nil
| All2_dep_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2
   * 'x * ('a, 'b, 'r, 'x) coq_All2_dep

val coq_All2_dep_rect :
  'a5 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
  coq_All2 -> 'a4 -> ('a1, 'a2, 'a3, 'a4) coq_All2_dep -> 'a5 -> 'a5) -> 'a1
  list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
  coq_All2_dep -> 'a5

val coq_All2_dep_rec :
  'a5 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
  coq_All2 -> 'a4 -> ('a1, 'a2, 'a3, 'a4) coq_All2_dep -> 'a5 -> 'a5) -> 'a1
  list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
  coq_All2_dep -> 'a5

type ('a, 'b, 'r, 'x) coq_All2_dep_sig = ('a, 'b, 'r, 'x) coq_All2_dep

val coq_All2_dep_sig_pack :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
  coq_All2_dep -> ('a1 list * ('a2 list * ('a1, 'a2, 'a3) coq_All2)) * ('a1,
  'a2, 'a3, 'a4) coq_All2_dep

val coq_All2_dep_Signature :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> (('a1, 'a2, 'a3, 'a4)
  coq_All2_dep, 'a1 list * ('a2 list * ('a1, 'a2, 'a3) coq_All2), ('a1, 'a2,
  'a3, 'a4) coq_All2_dep_sig) coq_Signature

val coq_NoConfusionHomPackage_All2_dep :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
  coq_All2_dep coq_NoConfusionPackage

val coq_Forall2_dep_sig_pack :
  'a1 list -> 'a2 list -> ('a1 list * ('a2 list * __)) * __

val coq_Forall2_dep_Signature :
  'a1 list -> 'a2 list -> ('a1 list * ('a2 list * __)) * __

type ('a, 'b, 'r) coq_All2i =
| All2i_nil
| All2i_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2i

val coq_All2i_rect :
  (nat -> 'a4) -> (nat -> 'a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1,
  'a2, 'a3) coq_All2i -> 'a4 -> 'a4) -> nat -> 'a1 list -> 'a2 list -> ('a1,
  'a2, 'a3) coq_All2i -> 'a4

val coq_All2i_rec :
  (nat -> 'a4) -> (nat -> 'a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1,
  'a2, 'a3) coq_All2i -> 'a4 -> 'a4) -> nat -> 'a1 list -> 'a2 list -> ('a1,
  'a2, 'a3) coq_All2i -> 'a4

type ('a, 'b, 'r) coq_All2i_sig = ('a, 'b, 'r) coq_All2i

val coq_All2i_sig_pack :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat * ('a1
  list * 'a2 list)) * ('a1, 'a2, 'a3) coq_All2i

val coq_All2i_Signature :
  nat -> 'a1 list -> 'a2 list -> (('a1, 'a2, 'a3) coq_All2i, nat * ('a1
  list * 'a2 list), ('a1, 'a2, 'a3) coq_All2i_sig) coq_Signature

val coq_NoConfusionHomPackage_All2i :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i
  coq_NoConfusionPackage

type ('a, 'b, 'c, 'r) coq_All3 =
| All3_nil
| All3_cons of 'a * 'b * 'c * 'a list * 'b list * 'c list * 'r
   * ('a, 'b, 'c, 'r) coq_All3

val coq_All3_rect :
  'a5 -> ('a1 -> 'a2 -> 'a3 -> 'a1 list -> 'a2 list -> 'a3 list -> 'a4 ->
  ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5 -> 'a5) -> 'a1 list -> 'a2 list -> 'a3
  list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5

val coq_All3_rec :
  'a5 -> ('a1 -> 'a2 -> 'a3 -> 'a1 list -> 'a2 list -> 'a3 list -> 'a4 ->
  ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5 -> 'a5) -> 'a1 list -> 'a2 list -> 'a3
  list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5

type ('a, 'b, 'c, 'r) coq_All3_sig = ('a, 'b, 'c, 'r) coq_All3

val coq_All3_sig_pack :
  'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> ('a1
  list * ('a2 list * 'a3 list)) * ('a1, 'a2, 'a3, 'a4) coq_All3

val coq_All3_Signature :
  'a1 list -> 'a2 list -> 'a3 list -> (('a1, 'a2, 'a3, 'a4) coq_All3, 'a1
  list * ('a2 list * 'a3 list), ('a1, 'a2, 'a3, 'a4) coq_All3_sig)
  coq_Signature

val coq_NoConfusionHomPackage_All3 :
  'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3
  coq_NoConfusionPackage

val coq_Forall2_rect :
  'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> 'a3 -> 'a3) ->
  'a1 list -> 'a2 list -> 'a3

val coq_Forall2_rec :
  'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> 'a3 -> 'a3) ->
  'a1 list -> 'a2 list -> 'a3

val coq_Forall2_dep_rect :
  'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> __ -> __ -> 'a3
  -> 'a3) -> 'a1 list -> 'a2 list -> 'a3

val coq_Forall2_dep_rec :
  'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> __ -> __ -> 'a3
  -> 'a3) -> 'a1 list -> 'a2 list -> 'a3

val alli : (nat -> 'a1 -> bool) -> nat -> 'a1 list -> bool

val allbiP :
  (nat -> 'a1 -> bool) -> nat -> 'a1 list -> (nat -> 'a1 -> 'a2 reflectT) ->
  ('a1, 'a2) coq_Alli reflectT

val alli_Alli :
  (nat -> 'a1 -> bool) -> nat -> 'a1 list -> (__, ('a1, __) coq_Alli) iffT

val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val forallbP : ('a1 -> bool) -> 'a1 list -> ('a1 -> reflect) -> reflect

val forallbP_cond :
  ('a1 -> bool) -> 'a1 list -> ('a1 -> __ -> reflect) -> reflect

val map_eq_inj : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 list -> ('a1, __) coq_All

val forallb2_All2 :
  ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> ('a1, 'a2, __) coq_All2

val coq_All2P :
  ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> ('a1, 'a2, __) coq_All2
  reflectT

val coq_All2_refl : 'a1 list -> ('a1 -> 'a2) -> ('a1, 'a1, 'a2) coq_All2

val coq_All2_map_equiv :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a1 list -> 'a2 list -> (('a1, 'a2, 'a5)
  coq_All2, ('a3, 'a4, 'a5) coq_All2) iffT

val coq_All2_map :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a5)
  coq_All2 -> ('a3, 'a4, 'a5) coq_All2

val coq_All2_map_inv :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a1 list -> 'a2 list -> ('a3, 'a4, 'a5)
  coq_All2 -> ('a1, 'a2, 'a5) coq_All2

val coq_All2_All_mix_left :
  'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a4) coq_All2 ->
  ('a1, 'a2, ('a3, 'a4) prod) coq_All2

val coq_All2_All_mix_right :
  'a1 list -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a2, 'a4) coq_All2 ->
  ('a1, 'a2, ('a4, 'a3) prod) coq_All2

val coq_All2i_All_mix_left :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a4)
  coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i

val coq_All2i_All_mix_right :
  nat -> 'a1 list -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a2, 'a4)
  coq_All2i -> ('a1, 'a2, ('a4, 'a3) prod) coq_All2i

val coq_All2i_All2_mix_left :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a4)
  coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i

val coq_Forall_All : 'a1 list -> ('a1, __) coq_All

val forallb_All : ('a1 -> bool) -> 'a1 list -> ('a1, __) coq_All

val coq_All_firstn :
  'a1 list -> nat -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All

val coq_All_skipn :
  'a1 list -> nat -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All

val coq_All_app :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All -> (('a1, 'a2) coq_All, ('a1,
  'a2) coq_All) prod

val coq_All_app_inv :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All -> ('a1,
  'a2) coq_All

val coq_All_True : 'a1 list -> ('a1, __) coq_All

val coq_All_tip : 'a1 -> ('a2, ('a1, 'a2) coq_All) iffT

val coq_All_mix :
  'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a3) coq_All -> ('a1, ('a2, 'a3)
  prod) coq_All

val coq_All2_All_left :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
  'a4) -> ('a1, 'a4) coq_All

val coq_All2_All_right :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
  'a4) -> ('a2, 'a4) coq_All

val coq_All2_right :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a2, 'a3) coq_All

val coq_All2_impl_All2 :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3 -> 'a4)
  coq_All2 -> ('a1, 'a2, 'a4) coq_All2

val coq_All2_impl :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
  'a4) -> ('a1, 'a2, 'a4) coq_All2

val coq_All2_eq_eq : 'a1 list -> 'a1 list -> ('a1, 'a1, __) coq_All2

val coq_All2_reflexivity :
  ('a1, 'a2) coq_Reflexive -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
  coq_Reflexive

val coq_All2_symmetry :
  ('a1, 'a2) coq_Symmetric -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
  coq_Symmetric

val coq_All2_transitivity :
  ('a1, 'a2) coq_Transitive -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
  coq_Transitive

val coq_All2_apply :
  'a2 list -> 'a3 list -> 'a1 -> ('a2, 'a3, 'a1 -> 'a4) coq_All2 -> ('a2,
  'a3, 'a4) coq_All2

val coq_All2_apply_arrow :
  'a2 list -> 'a3 list -> 'a1 -> ('a2, 'a3, 'a1 -> 'a4) coq_All2 -> ('a2,
  'a3, 'a4) coq_All2

val coq_All2_apply_dep_arrow :
  'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a3 -> 'a4)
  coq_All2 -> ('a1, 'a2, 'a4) coq_All2

val coq_All2_apply_dep_All :
  'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a3 -> 'a4)
  coq_All2 -> ('a2, 'a4) coq_All

val coq_All2i_All_left :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat -> 'a1 ->
  'a2 -> 'a3 -> 'a4) -> ('a1, 'a4) coq_All

val coq_All2i_All_right :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat -> 'a1 ->
  'a2 -> 'a3 -> 'a4) -> ('a2, 'a4) coq_All

val coq_All2_dep_impl :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
  coq_All2_dep -> ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> ('a1, 'a2, 'a3, 'a5)
  coq_All2_dep

val coq_All_refl : 'a1 list -> ('a1 -> 'a2) -> ('a1, 'a2) coq_All

val coq_All_rev_map :
  ('a2 -> 'a1) -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a3) coq_All

val coq_All_rev : 'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All

val coq_All_rev_inv : 'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All

val coq_All_impl_All :
  'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2 -> 'a3) coq_All -> ('a1, 'a3)
  coq_All

val coq_Alli_impl_Alli :
  'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2 -> 'a3) coq_Alli ->
  ('a1, 'a3) coq_Alli

val coq_All_impl :
  'a1 list -> ('a1, 'a2) coq_All -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All

val coq_Alli_impl :
  'a1 list -> nat -> ('a1, 'a2) coq_Alli -> (nat -> 'a1 -> 'a2 -> 'a3) ->
  ('a1, 'a3) coq_Alli

val coq_All_map :
  ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a3) coq_All -> ('a2, 'a3) coq_All

val coq_All_map_inv :
  ('a1 -> 'a2) -> 'a1 list -> ('a2, 'a3) coq_All -> ('a1, 'a3) coq_All

val coq_In_All : 'a1 list -> ('a1 -> __ -> 'a2) -> ('a1, 'a2) coq_All

val coq_All_nth_error : 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_All -> 'a2

val coq_Alli_mix :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a3) coq_Alli -> ('a1,
  ('a2, 'a3) prod) coq_Alli

val coq_Alli_All :
  'a1 list -> nat -> ('a1, 'a2) coq_Alli -> (nat -> 'a1 -> 'a2 -> 'a3) ->
  ('a1, 'a3) coq_All

val coq_Alli_app :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Alli -> (('a1, 'a2) coq_Alli,
  ('a1, 'a2) coq_Alli) prod

val coq_Alli_nth_error :
  nat -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2

val forall_nth_error_All :
  'a1 list -> (nat -> 'a1 -> __ -> 'a2) -> ('a1, 'a2) coq_All

val forall_nth_error_Alli :
  nat -> 'a1 list -> (nat -> 'a1 -> __ -> 'a2) -> ('a1, 'a2) coq_Alli

val coq_Alli_mapi :
  (nat -> 'a1 -> 'a2) -> nat -> 'a1 list -> (('a1, 'a3) coq_Alli, ('a2, 'a3)
  coq_Alli) iffT

val coq_Alli_shift :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli

val coq_Alli_rev :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli

val coq_Alli_rev_inv :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli

val coq_Alli_app_inv :
  'a1 list -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli
  -> ('a1, 'a2) coq_Alli

val coq_Alli_rev_nth_error :
  'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2

val coq_Alli_shiftn :
  nat -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli

val coq_Alli_shiftn_inv :
  nat -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli

val coq_Alli_All_mix :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a3) coq_All -> ('a1, ('a2,
  'a3) prod) coq_Alli

type ('a, 'p) coq_OnOne2 =
| OnOne2_hd of 'a * 'a * 'a list * 'p
| OnOne2_tl of 'a * 'a list * 'a list * ('a, 'p) coq_OnOne2

val coq_OnOne2_rect :
  ('a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 list ->
  ('a1, 'a2) coq_OnOne2 -> 'a3 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1, 'a2)
  coq_OnOne2 -> 'a3

val coq_OnOne2_rec :
  ('a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 list ->
  ('a1, 'a2) coq_OnOne2 -> 'a3 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1, 'a2)
  coq_OnOne2 -> 'a3

type ('a, 'p) coq_OnOne2_sig = ('a, 'p) coq_OnOne2

val coq_OnOne2_sig_pack :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1 list * 'a1
  list) * ('a1, 'a2) coq_OnOne2

val coq_OnOne2_Signature :
  'a1 list -> 'a1 list -> (('a1, 'a2) coq_OnOne2, 'a1 list * 'a1 list, ('a1,
  'a2) coq_OnOne2_sig) coq_Signature

val coq_NoConfusionPackage_OnOne2 :
  (('a1 list * 'a1 list) * ('a1, 'a2) coq_OnOne2) coq_NoConfusionPackage

val coq_OnOne2_All_mix_left :
  'a1 list -> 'a1 list -> ('a1, 'a3) coq_All -> ('a1, 'a2) coq_OnOne2 ->
  ('a1, ('a2, 'a3) prod) coq_OnOne2

val coq_OnOne2_app :
  'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a2)
  coq_OnOne2

val coq_OnOne2_app_r :
  'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a2)
  coq_OnOne2

val coq_OnOne2_mapP :
  'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, __) coq_OnOne2 -> ('a2, __)
  coq_OnOne2

val coq_OnOne2_map :
  'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, ('a2, 'a1, 'a3) on_Trel)
  coq_OnOne2 -> ('a2, 'a3) coq_OnOne2

val coq_OnOne2_sym :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a2) coq_OnOne2

val coq_OnOne2_exist :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1 -> 'a1 -> 'a2 ->
  ('a1, ('a3, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a3) coq_OnOne2, ('a1,
  'a3) coq_OnOne2) prod) sigT

val coq_OnOne2_ind_l :
  ('a1 list -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 list -> 'a1 ->
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> 'a3 -> 'a3) -> 'a1 list ->
  'a1 list -> ('a1, 'a2) coq_OnOne2 -> 'a3

val coq_OnOne2_impl_exist_and_All :
  'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a1,
  'a3) coq_All2 -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 -> ('a1, ('a4, 'a3) prod)
  sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2, ('a1, 'a1, 'a3) coq_All2) prod)
  sigT

val coq_OnOne2_impl_exist_and_All_r :
  'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a1,
  'a3) coq_All2 -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 -> ('a1, ('a4, 'a3) prod)
  sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2, ('a1, 'a1, 'a3) coq_All2) prod)
  sigT

val coq_OnOne2_split :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, ('a1, ('a1 list,
  ('a1 list, ('a2, __) prod) sigT) sigT) sigT) sigT

val coq_OnOne2_impl :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1 -> 'a1 -> 'a2 -> 'a3)
  -> ('a1, 'a3) coq_OnOne2

val coq_OnOne2_nth_error :
  'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2 -> ('a1, (__,
  (__, 'a2) sum) prod) sigT

val coq_OnOne2_nth_error_r :
  'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2 -> ('a1, (__,
  (__, 'a2) sum) prod) sigT

val coq_OnOne2_impl_All_r :
  'a1 list -> 'a1 list -> ('a1 -> 'a1 -> 'a3 -> 'a2 -> 'a3) -> ('a1, 'a2)
  coq_OnOne2 -> ('a1, 'a3) coq_All -> ('a1, 'a3) coq_All

val coq_OnOne2_All2_All2 :
  'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a1,
  'a3) coq_All2 -> ('a1 -> 'a1 -> 'a3 -> 'a4) -> ('a1 -> 'a1 -> 'a1 -> 'a2 ->
  'a3 -> 'a4) -> ('a1, 'a1, 'a4) coq_All2

val coq_OnOne2_All_All :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a3) coq_All -> ('a1
  -> 'a3 -> 'a4) -> ('a1 -> 'a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a4) coq_All

type ('a, 'p) coq_OnOne2i =
| OnOne2i_hd of nat * 'a * 'a * 'a list * 'p
| OnOne2i_tl of nat * 'a * 'a list * 'a list * ('a, 'p) coq_OnOne2i

val coq_OnOne2i_rect :
  (nat -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> (nat -> 'a1 -> 'a1 list ->
  'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 -> 'a3) -> nat -> 'a1 list -> 'a1
  list -> ('a1, 'a2) coq_OnOne2i -> 'a3

val coq_OnOne2i_rec :
  (nat -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> (nat -> 'a1 -> 'a1 list ->
  'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 -> 'a3) -> nat -> 'a1 list -> 'a1
  list -> ('a1, 'a2) coq_OnOne2i -> 'a3

type ('a, 'p) coq_OnOne2i_sig = ('a, 'p) coq_OnOne2i

val coq_OnOne2i_sig_pack :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat * ('a1
  list * 'a1 list)) * ('a1, 'a2) coq_OnOne2i

val coq_OnOne2i_Signature :
  nat -> 'a1 list -> 'a1 list -> (('a1, 'a2) coq_OnOne2i, nat * ('a1
  list * 'a1 list), ('a1, 'a2) coq_OnOne2i_sig) coq_Signature

val coq_NoConfusionPackage_OnOne2i :
  ((nat * ('a1 list * 'a1 list)) * ('a1, 'a2) coq_OnOne2i)
  coq_NoConfusionPackage

val coq_OnOne2i_All_mix_left :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a3) coq_All -> ('a1, 'a2) coq_OnOne2i
  -> ('a1, ('a2, 'a3) prod) coq_OnOne2i

val coq_OnOne2i_app :
  nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> ('a1,
  'a2) coq_OnOne2i

val coq_OnOne2i_app_r :
  nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> ('a1,
  'a2) coq_OnOne2i

val coq_OnOne2i_mapP :
  nat -> 'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, __) coq_OnOne2i ->
  ('a2, __) coq_OnOne2i

val coq_OnOne2i_map :
  nat -> 'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, ('a2, 'a1, 'a3)
  on_Trel) coq_OnOne2i -> ('a2, 'a3) coq_OnOne2i

val coq_OnOne2i_sym :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> ('a1, 'a2)
  coq_OnOne2i

val coq_OnOne2i_exist :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat -> 'a1 -> 'a1
  -> 'a2 -> ('a1, ('a3, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a3)
  coq_OnOne2i, ('a1, 'a3) coq_OnOne2i) prod) sigT

val coq_OnOne2i_ind_l :
  ('a1 list -> nat -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 list ->
  nat -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 -> 'a3)
  -> nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3

val coq_OnOne2i_impl_exist_and_All :
  nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> ('a1,
  'a1, 'a3) coq_All2 -> (nat -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 -> ('a1,
  ('a4, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2i, ('a1, 'a1,
  'a3) coq_All2) prod) sigT

val coq_OnOne2i_impl_exist_and_All_r :
  nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> ('a1,
  'a1, 'a3) coq_All2 -> (nat -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 -> ('a1,
  ('a4, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2i, ('a1, 'a1,
  'a3) coq_All2) prod) sigT

val coq_OnOne2i_split :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat, ('a1, ('a1,
  ('a1 list, ('a1 list, ('a2, __) prod) sigT) sigT) sigT) sigT) sigT

val coq_OnOne2i_impl :
  nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat -> 'a1 -> 'a1
  -> 'a2 -> 'a3) -> ('a1, 'a3) coq_OnOne2i

val coq_OnOne2i_nth_error :
  'a1 list -> 'a1 list -> nat -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2i ->
  ('a1, (__, (__, 'a2) sum) prod) sigT

val coq_OnOne2i_nth_error_r :
  nat -> 'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2i ->
  ('a1, (__, (__, 'a2) sum) prod) sigT

type ('a, 'b, 'p) coq_OnOne2All =
| OnOne2All_hd of 'b * 'b list * 'a * 'a * 'a list * 'p
| OnOne2All_tl of 'b * 'b list * 'a * 'a list * 'a list
   * ('a, 'b, 'p) coq_OnOne2All

val coq_OnOne2All_rect :
  ('a2 -> 'a2 list -> 'a1 -> 'a1 -> 'a1 list -> 'a3 -> __ -> 'a4) -> ('a2 ->
  'a2 list -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All ->
  'a4 -> 'a4) -> 'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> 'a4

val coq_OnOne2All_rec :
  ('a2 -> 'a2 list -> 'a1 -> 'a1 -> 'a1 list -> 'a3 -> __ -> 'a4) -> ('a2 ->
  'a2 list -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All ->
  'a4 -> 'a4) -> 'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> 'a4

type ('a, 'b, 'p) coq_OnOne2All_sig = ('a, 'b, 'p) coq_OnOne2All

val coq_OnOne2All_sig_pack :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a2
  list * ('a1 list * 'a1 list)) * ('a1, 'a2, 'a3) coq_OnOne2All

val coq_OnOne2All_Signature :
  'a2 list -> 'a1 list -> 'a1 list -> (('a1, 'a2, 'a3) coq_OnOne2All, 'a2
  list * ('a1 list * 'a1 list), ('a1, 'a2, 'a3) coq_OnOne2All_sig)
  coq_Signature

val coq_NoConfusionPackage_OnOne2All :
  (('a2 list * ('a1 list * 'a1 list)) * ('a1, 'a2, 'a3) coq_OnOne2All)
  coq_NoConfusionPackage

val coq_OnOne2All_All_mix_left :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a4) coq_All -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> ('a1, 'a2, ('a3, 'a4) prod) coq_OnOne2All

val coq_OnOne2All_All2_mix_left :
  'a2 list -> 'a1 list -> 'a1 list -> ('a2, 'a1, 'a4) coq_All2 -> ('a1, 'a2,
  'a3) coq_OnOne2All -> ('a1, 'a2, ('a3, 'a4) prod) coq_OnOne2All

val coq_OnOne2All_app :
  'a2 list -> 'a2 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> ('a1, 'a2, 'a3) coq_OnOne2All

val coq_OnOne2All_mapP :
  'a3 list -> 'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, 'a3, __)
  coq_OnOne2All -> ('a2, 'a3, __) coq_OnOne2All

val coq_OnOne2All_map :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1 -> 'a3) -> ('a1, 'a2, ('a3, 'a1,
  'a4) on_Trel) coq_OnOne2All -> ('a3, 'a2, 'a4) coq_OnOne2All

val coq_OnOne2All_map_all :
  'a3 list -> 'a1 list -> 'a1 list -> ('a3 -> 'a4) -> ('a1 -> 'a2) -> ('a1,
  'a3, ('a2, 'a1, 'a5) on_Trel) coq_OnOne2All -> ('a2, 'a4, 'a5) coq_OnOne2All

val coq_OnOne2All_sym :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a1,
  'a2, 'a3) coq_OnOne2All

val coq_OnOne2All_exist :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a2
  -> 'a1 -> 'a1 -> 'a3 -> ('a1, ('a4, 'a4) prod) sigT) -> ('a1 list, (('a1,
  'a2, 'a4) coq_OnOne2All, ('a1, 'a2, 'a4) coq_OnOne2All) prod) sigT

val coq_OnOne2All_ind_l :
  ('a1 list -> 'a2 -> 'a2 list -> 'a1 -> 'a1 -> 'a1 list -> 'a3 -> __ -> 'a4)
  -> ('a1 list -> 'a2 -> 'a2 list -> 'a1 -> 'a1 list -> 'a1 list -> ('a1,
  'a2, 'a3) coq_OnOne2All -> 'a4 -> 'a4) -> 'a2 list -> 'a1 list -> 'a1 list
  -> ('a1, 'a2, 'a3) coq_OnOne2All -> 'a4

val coq_OnOne2All_impl_exist_and_All :
  'a2 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> ('a1, 'a1, 'a4) coq_All2 -> ('a2 -> 'a1 -> 'a1 -> 'a1 ->
  'a3 -> 'a4 -> ('a1, ('a5, 'a4) prod) sigT) -> ('a1 list, (('a1, 'a2, 'a5)
  coq_OnOne2All, ('a1, 'a1, 'a4) coq_All2) prod) sigT

val coq_OnOne2All_impl_exist_and_All_r :
  'a2 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> ('a1, 'a1, 'a4) coq_All2 -> ('a2 -> 'a1 -> 'a1 -> 'a1 ->
  'a3 -> 'a4 -> ('a1, ('a5, 'a4) prod) sigT) -> ('a1 list, (('a1, 'a2, 'a5)
  coq_OnOne2All, ('a1, 'a1, 'a4) coq_All2) prod) sigT

val coq_OnOne2All_split :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a2,
  ('a1, ('a1, ('a1 list, ('a1 list, ('a3, __) prod) sigT) sigT) sigT) sigT)
  sigT

val coq_OnOne2All_impl :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a2
  -> 'a1 -> 'a1 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_OnOne2All

val coq_OnOne2All_nth_error :
  'a2 list -> 'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> ('a1, (__, (__, ('a2, (__, 'a3) prod) sigT) sum) prod) sigT

val coq_OnOne2All_nth_error_r :
  'a2 list -> 'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2, 'a3)
  coq_OnOne2All -> ('a1, (__, (__, ('a2, (__, 'a3) prod) sigT) sum) prod) sigT

val coq_OnOne2All_impl_All_r :
  'a2 list -> 'a1 list -> 'a1 list -> ('a2 -> 'a1 -> 'a1 -> 'a4 -> 'a3 ->
  'a4) -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a1, 'a4) coq_All -> ('a1, 'a4)
  coq_All

val coq_OnOne2All_nth_error_impl :
  'a1 list -> 'a2 list -> 'a2 list -> ('a2, 'a1, 'a3) coq_OnOne2All -> ('a2,
  'a1, ((nat, __) sigT, 'a3) prod) coq_OnOne2All

val coq_Forall2_All2 : 'a1 list -> 'a2 list -> ('a1, 'a2, __) coq_All2

val coq_All2_map_left_equiv :
  'a2 list -> 'a3 list -> ('a2 -> 'a1) -> (('a2, 'a3, 'a4) coq_All2, ('a1,
  'a3, 'a4) coq_All2) iffT

val coq_All2_map_right_equiv :
  'a1 list -> 'a2 list -> ('a2 -> 'a3) -> (('a1, 'a2, 'a4) coq_All2, ('a1,
  'a3, 'a4) coq_All2) iffT

val coq_All2_map_left :
  'a2 list -> 'a3 list -> ('a2 -> 'a1) -> ('a2, 'a3, 'a4) coq_All2 -> ('a1,
  'a3, 'a4) coq_All2

val coq_All2_map_right :
  'a1 list -> 'a2 list -> ('a2 -> 'a3) -> ('a1, 'a2, 'a4) coq_All2 -> ('a1,
  'a3, 'a4) coq_All2

val coq_All2_map_left_inv :
  'a2 list -> 'a3 list -> ('a2 -> 'a1) -> ('a1, 'a3, 'a4) coq_All2 -> ('a2,
  'a3, 'a4) coq_All2

val coq_All2_map_right_inv :
  'a1 list -> 'a2 list -> ('a2 -> 'a3) -> ('a1, 'a3, 'a4) coq_All2 -> ('a1,
  'a2, 'a4) coq_All2

val coq_All2_undep :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> (('a1, 'a2, 'a4)
  coq_All2, ('a1, 'a2, 'a3, 'a4) coq_All2_dep) iffT

val coq_All2_All2_mix :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a4)
  coq_All2 -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2

val coq_All2_mix :
  'a1 list -> 'a1 list -> ('a1, 'a1, 'a2) coq_All2 -> ('a1, 'a1, 'a3)
  coq_All2 -> ('a1, 'a1, ('a2, 'a3) prod) coq_All2

val coq_All2_mix_inv :
  'a1 list -> 'a1 list -> ('a1, 'a1, ('a2, 'a3) prod) coq_All2 -> (('a1, 'a1,
  'a2) coq_All2, ('a1, 'a1, 'a3) coq_All2) prod

val coq_All_safe_nth : 'a1 list -> nat -> ('a1, 'a2) coq_All -> 'a2

type size = nat

val all_size : ('a1 -> 'a2 -> size) -> 'a1 list -> ('a1, 'a2) coq_All -> size

val alli_size :
  (nat -> 'a1 -> 'a2 -> size) -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli ->
  size

val all2_size :
  ('a1 -> 'a2 -> 'a3 -> size) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
  coq_All2 -> size

val all2i_size :
  (nat -> 'a1 -> 'a2 -> 'a3 -> size) -> nat -> 'a1 list -> 'a2 list -> ('a1,
  'a2, 'a3) coq_All2i -> size

val coq_All2i_impl :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat -> 'a1 ->
  'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_All2i

val nth_error_all : 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_All -> 'a2

val nth_error_alli :
  'a1 list -> nat -> 'a1 -> nat -> ('a1, 'a2) coq_Alli -> 'a2

val map_option_Some :
  'a1 option list -> 'a1 list -> ('a1 option, 'a1, __) coq_All2

val coq_All_mapi :
  (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> ('a1, 'a3) coq_Alli -> ('a2, 'a3)
  coq_All

val coq_All_Alli :
  'a1 list -> nat -> ('a1, 'a2) coq_All -> (nat -> 'a1 -> 'a2 -> 'a3) ->
  ('a1, 'a3) coq_Alli

val coq_All2_All_left_pack :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, ('a2, (__, 'a3)
  prod) sigT) coq_Alli

val map_option_out_All :
  'a1 option list -> 'a1 list -> ('a1 option, __) coq_All -> ('a1, __) coq_All

val coq_All2_app_inv_l :
  'a1 list -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a2 list,
  ('a2 list, (__, (('a1, 'a2, 'a3) coq_All2, ('a1, 'a2, 'a3) coq_All2) prod)
  prod) sigT) sigT

val coq_All2_app_inv_r :
  'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 list,
  ('a1 list, (__, (('a1, 'a2, 'a3) coq_All2, ('a1, 'a2, 'a3) coq_All2) prod)
  prod) sigT) sigT

val coq_All2_app_inv :
  'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 ->
  (('a1, 'a2, 'a3) coq_All2, ('a1, 'a2, 'a3) coq_All2) prod

val coq_All2_rect_rev :
  'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
  coq_All2 -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2
  -> 'a4

val coq_All2_app :
  'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 ->
  ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3) coq_All2

val coq_All2_rev :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3) coq_All2

val coq_All_All2_flex :
  'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1 -> 'a2 -> __ -> 'a3 ->
  'a4) -> ('a1, 'a2, 'a4) coq_All2

val coq_All_All_All2 :
  'a1 list -> 'a1 list -> ('a1, __) coq_All -> ('a1, __) coq_All -> ('a1,
  'a1, __) coq_All2

val coq_All2_impl_In :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> __ -> __
  -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_All2

val coq_All2_All : 'a1 list -> ('a1, 'a1, 'a2) coq_All2 -> ('a1, 'a2) coq_All

val coq_All2_trans :
  ('a1, 'a2) coq_Transitive -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
  coq_Transitive

val coq_All2_trans' :
  ('a1 -> 'a2 -> 'a3 -> ('a4, 'a5) prod -> 'a6) -> 'a1 list -> 'a2 list ->
  'a3 list -> ('a1, 'a2, 'a4) coq_All2 -> ('a2, 'a3, 'a5) coq_All2 -> ('a1,
  'a3, 'a6) coq_All2

val coq_All2_nth :
  'a1 list -> 'a2 list -> nat -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 ->
  'a3 -> 'a3

val coq_All2_mapi :
  (nat -> 'a1 -> 'a3) -> (nat -> 'a2 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1,
  'a2, nat -> 'a5) coq_All2 -> ('a3, 'a4, 'a5) coq_All2

val coq_All2_skipn :
  'a1 list -> 'a2 list -> nat -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3)
  coq_All2

val coq_All2_right_triv :
  'a1 list -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a2, 'a3) coq_All2

val coq_All_repeat : nat -> 'a1 -> 'a2 -> ('a1, 'a2) coq_All

val coq_All2_from_nth_error :
  'a1 list -> 'a2 list -> (nat -> 'a1 -> 'a2 -> __ -> __ -> __ -> 'a3) ->
  ('a1, 'a2, 'a3) coq_All2

val coq_All2_nth_error :
  'a1 list -> 'a2 list -> nat -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 -> 'a3

val coq_All2_dep_from_nth_error :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> (nat -> 'a1 -> 'a2 ->
  __ -> __ -> __ -> 'a4) -> ('a1, 'a2, 'a3, 'a4) coq_All2_dep

val coq_All2_dep_nth_error :
  'a1 list -> 'a2 list -> nat -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 ->
  ('a1, 'a2, 'a3, 'a4) coq_All2_dep -> 'a4

val coq_All2_swap :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a2, 'a1, 'a3) coq_All2

val coq_All2_firstn :
  'a1 list -> 'a2 list -> nat -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3)
  coq_All2

val coq_All2_impl' :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2 -> 'a3 ->
  'a4) coq_All -> ('a1, 'a2, 'a4) coq_All2

val coq_All_All2 :
  'a1 list -> ('a1, 'a3) coq_All -> ('a1 -> 'a3 -> 'a2) -> ('a1, 'a1, 'a2)
  coq_All2

val coq_All2_nth_error_Some :
  'a1 list -> 'a2 list -> nat -> 'a1 -> ('a1, 'a2, 'a3) coq_All2 -> ('a2,
  (__, 'a3) prod) sigT

val coq_All2_nth_error_Some_r :
  'a1 list -> 'a2 list -> nat -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 -> ('a1,
  (__, 'a3) prod) sigT

val coq_All2_same : 'a1 list -> ('a1 -> 'a2) -> ('a1, 'a1, 'a2) coq_All2

val coq_All2_prod :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a4)
  coq_All2 -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2

val coq_All2_prod_inv :
  'a1 list -> 'a2 list -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2 -> (('a1, 'a2,
  'a3) coq_All2, ('a1, 'a2, 'a4) coq_All2) prod

val coq_All2_sym :
  'a1 list -> 'a1 list -> ('a1, 'a1, 'a2) coq_All2 -> ('a1, 'a1, 'a2) coq_All2

val coq_All2_symP :
  ('a1, 'a2) coq_Symmetric -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
  coq_Symmetric

val coq_All_All2_All2_mix :
  'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2 -> 'a2 -> 'a4 -> 'a5 -> ('a2,
  ('a3, 'a3) prod) sigT) coq_All -> ('a1, 'a2, 'a4) coq_All2 -> ('a1, 'a2,
  'a5) coq_All2 -> ('a2 list, (('a2, 'a2, 'a3) coq_All2, ('a2, 'a2, 'a3)
  coq_All2) prod) sigT

val coq_All2_nth_error_Some_right :
  'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a1, 'a2) coq_All2 -> ('a1,
  (__, 'a2) prod) sigT

val forallb_nth' : 'a1 list -> ('a1 -> bool) -> nat -> 'a1 -> sumbool

val coq_All_prod_inv :
  'a1 list -> ('a1, ('a2, 'a3) prod) coq_All -> (('a1, 'a2) coq_All, ('a1,
  'a3) coq_All) prod

val coq_All_pair :
  'a1 list -> (('a1, ('a2, 'a3) prod) coq_All, (('a1, 'a2) coq_All, ('a1,
  'a3) coq_All) prod) iffT

val coq_All_prod :
  'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a3) coq_All -> ('a1, ('a2, 'a3)
  prod) coq_All

val coq_All2i_mapi :
  (nat -> 'a1 -> 'a3) -> (nat -> 'a2 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1,
  'a2, 'a5) coq_All2i -> ('a3, 'a4, 'a5) coq_All2i

val coq_All2i_app :
  nat -> 'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3)
  coq_All2i -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, 'a3) coq_All2i

val coq_All2i_mapi_rec :
  'a3 list -> 'a4 list -> (nat -> 'a3 -> 'a1) -> (nat -> 'a4 -> 'a2) -> nat
  -> ('a3, 'a4, 'a5) coq_All2i -> ('a1, 'a2, 'a5) coq_All2i

val coq_All2i_trivial :
  (nat -> 'a1 -> 'a2 -> 'a3) -> nat -> 'a1 list -> 'a2 list -> ('a1, 'a2,
  'a3) coq_All2i

val coq_All2i_rev :
  'a1 list -> 'a2 list -> nat -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, 'a3)
  coq_All2i

type ('a, 'b, 'r) coq_All2i_len =
| All2i_len_nil
| All2i_len_cons of 'a * 'b * 'a list * 'b list * 'r
   * ('a, 'b, 'r) coq_All2i_len

val coq_All2i_len_rect :
  'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
  coq_All2i_len -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
  coq_All2i_len -> 'a4

val coq_All2i_len_rec :
  'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
  coq_All2i_len -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
  coq_All2i_len -> 'a4

val coq_All2i_len_app :
  'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3)
  coq_All2i_len -> ('a1, 'a2, 'a3) coq_All2i_len -> ('a1, 'a2, 'a3)
  coq_All2i_len

val coq_All2i_len_impl :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i_len -> (nat -> 'a1 -> 'a2
  -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_All2i_len

val coq_All2i_len_rev :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i_len -> ('a1, 'a2, 'a3)
  coq_All2i_len

val coq_All2i_rev_ctx :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i_len -> ('a1, 'a2,
  'a3) coq_All2i

val coq_All2i_rev_ctx_gen :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, 'a3)
  coq_All2i_len

val coq_All2i_rev_ctx_inv :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, 'a3)
  coq_All2i_len

val coq_All_All2_refl :
  'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a1, 'a2) coq_All2

val coq_All2_app_r :
  'a1 list -> 'a1 list -> 'a1 -> 'a1 -> ('a1, 'a1, 'a2) coq_All2 -> (('a1,
  'a1, 'a2) coq_All2, 'a2) prod

val forallb2P :
  ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> ('a1 -> 'a2 -> reflect) ->
  reflect

val coq_All_forall : 'a1 list -> ('a1, __) coq_All -> 'a2 -> ('a1, __) coq_All

val coq_All2i_map :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> nat -> 'a1 list -> 'a2 list -> ('a1, 'a2,
  'a5) coq_All2i -> ('a3, 'a4, 'a5) coq_All2i

val coq_All2i_map_right :
  ('a1 -> 'a3) -> nat -> 'a2 list -> 'a1 list -> ('a2, 'a1, 'a4) coq_All2i ->
  ('a2, 'a3, 'a4) coq_All2i

val coq_All2i_nth_impl_gen :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, (__,
  'a3) prod) coq_All2i

val coq_All2i_nth_hyp :
  'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, (__, 'a3)
  prod) coq_All2i

val coq_All2i_nth_error_l :
  'a1 list -> 'a2 list -> nat -> 'a1 -> nat -> ('a1, 'a2, 'a3) coq_All2i ->
  ('a2, (__, 'a3) prod) sigT

val coq_All2i_nth_error_r :
  'a1 list -> 'a2 list -> nat -> 'a2 -> nat -> ('a1, 'a2, 'a3) coq_All2i ->
  ('a1, (__, 'a3) prod) sigT

val coq_All2i_app_inv_l :
  nat -> 'a1 list -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i ->
  ('a2 list, ('a2 list, (__, (('a1, 'a2, 'a3) coq_All2i, ('a1, 'a2, 'a3)
  coq_All2i) prod) prod) sigT) sigT

val coq_All2i_app_inv_r :
  nat -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i ->
  ('a1 list, ('a1 list, (__, (('a1, 'a2, 'a3) coq_All2i, ('a1, 'a2, 'a3)
  coq_All2i) prod) prod) sigT) sigT

val coq_All2i_app_inv :
  nat -> 'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3)
  coq_All2i -> (('a1, 'a2, 'a3) coq_All2i, ('a1, 'a2, 'a3) coq_All2i) prod

val coq_All2i_All2_All2i_All2i :
  nat -> 'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a4) coq_All2i ->
  ('a2, 'a3, 'a5) coq_All2 -> ('a1, 'a3, 'a6) coq_All2i -> (nat -> 'a1 -> 'a2
  -> 'a3 -> 'a4 -> 'a5 -> 'a6 -> 'a7) -> ('a1, 'a3, 'a7) coq_All2i

val coq_All2i_All2_All2 :
  nat -> 'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a4) coq_All2i ->
  ('a2, 'a3, 'a5) coq_All2 -> (nat -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'a6)
  -> ('a2, 'a3, 'a6) coq_All2

type ('a, 'p) coq_All_fold =
| All_fold_nil
| All_fold_cons of 'a * 'a list * ('a, 'p) coq_All_fold * 'p

val coq_All_fold_rect :
  'a3 -> ('a1 -> 'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3 -> 'a2 -> 'a3) ->
  'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3

val coq_All_fold_rec :
  'a3 -> ('a1 -> 'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3 -> 'a2 -> 'a3) ->
  'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3

type ('a, 'p) coq_All_fold_sig = ('a, 'p) coq_All_fold

val coq_All_fold_sig_pack :
  'a1 list -> ('a1, 'a2) coq_All_fold -> 'a1 list * ('a1, 'a2) coq_All_fold

val coq_All_fold_Signature :
  'a1 list -> (('a1, 'a2) coq_All_fold, 'a1 list, ('a1, 'a2)
  coq_All_fold_sig) coq_Signature

val coq_NoConfusionHomPackage_All_fold :
  'a1 list -> ('a1, 'a2) coq_All_fold coq_NoConfusionPackage

type ('a, 'p) coq_All2_fold =
| All2_fold_nil
| All2_fold_cons of 'a * 'a * 'a list * 'a list * ('a, 'p) coq_All2_fold * 'p

val coq_All2_fold_rect :
  'a3 -> ('a1 -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
  'a3 -> 'a2 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
  'a3

val coq_All2_fold_rec :
  'a3 -> ('a1 -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
  'a3 -> 'a2 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
  'a3

type ('a, 'p) coq_All2_fold_sig = ('a, 'p) coq_All2_fold

val coq_All2_fold_sig_pack :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list * 'a1
  list) * ('a1, 'a2) coq_All2_fold

val coq_All2_fold_Signature :
  'a1 list -> 'a1 list -> (('a1, 'a2) coq_All2_fold, 'a1 list * 'a1 list,
  ('a1, 'a2) coq_All2_fold_sig) coq_Signature

val coq_NoConfusionPackage_All2_fold :
  (('a1 list * 'a1 list) * ('a1, 'a2) coq_All2_fold) coq_NoConfusionPackage

type ('a, 'b, 'p) coq_All_over = 'p

val coq_All2_fold_from_nth_error :
  'a1 list -> 'a1 list -> (nat -> 'a1 -> 'a1 -> __ -> __ -> __ -> 'a2) ->
  ('a1, 'a2) coq_All2_fold

val coq_All2_fold_app :
  'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
  ('a1, ('a1, 'a1, 'a2) coq_All_over) coq_All2_fold -> ('a1, 'a2)
  coq_All2_fold

val coq_All2_fold_impl :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
  -> 'a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold

val coq_All_fold_app_inv :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> (('a1, 'a2)
  coq_All_fold, ('a1, 'a2) coq_All_fold) prod

val coq_All2_fold_All_fold_mix_left :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a3) coq_All2_fold
  -> ('a1, ('a2, 'a3) prod) coq_All2_fold

val coq_All2_fold_All_fold_mix_right :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a3) coq_All2_fold
  -> ('a1, ('a2, 'a3) prod) coq_All2_fold

val coq_All2_fold_All_fold_mix_left_inv :
  'a1 list -> 'a1 list -> ('a1, ('a2, 'a3) prod) coq_All2_fold -> (('a1, 'a2)
  coq_All_fold, ('a1, 'a3) coq_All2_fold) prod

val coq_All2_fold_All_right :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a2) coq_All_fold

val coq_All2_fold_All_left :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a2) coq_All_fold

val coq_All_fold_impl :
  'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1 list -> 'a1 -> 'a2 -> 'a3) ->
  ('a1, 'a3) coq_All_fold

val coq_All_fold_app :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a2) coq_All_fold
  -> ('a1, 'a2) coq_All_fold

val coq_Alli_All_fold :
  nat -> 'a1 list -> (('a1, 'a2) coq_Alli, ('a1, 'a2) coq_All_fold) iffT

val coq_Alli_rev_All_fold :
  nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_All_fold

val coq_All_fold_Alli_rev :
  nat -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a2) coq_Alli

val coq_All2_fold_All2 :
  'a1 list -> 'a1 list -> (('a1, 'a2) coq_All2_fold, ('a1, 'a1, 'a2)
  coq_All2) iffT

val coq_All2_fold_refl :
  ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> ('a1, 'a2) coq_All2_fold

val coq_All2_fold_trans :
  ('a1 list -> 'a1 list -> 'a1 list -> 'a1 -> 'a1 -> 'a1 -> ('a1, 'a2)
  coq_All2_fold -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a2) coq_All2_fold ->
  'a2 -> 'a2 -> 'a2) -> ('a1 list, ('a1, 'a2) coq_All2_fold) coq_Transitive

val coq_All2_fold_sym :
  ('a1 list -> 'a1 list -> 'a1 -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1,
  'a2) coq_All2_fold -> 'a2 -> 'a2) -> ('a1 list, ('a1, 'a2) coq_All2_fold)
  coq_Symmetric

val coq_All2_fold_app_inv :
  'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
  (('a1, 'a2) coq_All2_fold, ('a1, 'a2) coq_All2_fold) prod

val coq_All2_fold_app_inv_l :
  'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
  (('a1, 'a2) coq_All2_fold, ('a1, 'a2) coq_All2_fold) prod

val coq_All2_fold_impl_ind :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
  -> 'a1 -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3) coq_All2_fold ->
  'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold

val coq_All2_fold_impl_len :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
  -> 'a1 -> 'a1 -> __ -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold

val coq_All2_fold_nth :
  nat -> 'a1 list -> 'a1 list -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1,
  (__, (('a1, 'a2) coq_All2_fold, 'a2) prod) prod) sigT

val coq_All2_fold_nth_r :
  nat -> 'a1 list -> 'a1 list -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1,
  (__, (('a1, 'a2) coq_All2_fold, 'a2) prod) prod) sigT

val coq_All2_fold_prod :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3)
  coq_All2_fold -> ('a1, ('a2, 'a3) prod) coq_All2_fold

val coq_All2_fold_prod_inv :
  'a1 list -> 'a1 list -> ('a1, ('a2, 'a3) prod) coq_All2_fold -> (('a1, 'a2)
  coq_All2_fold, ('a1, 'a3) coq_All2_fold) prod

val coq_All_fold_prod :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a2) coq_All_fold
  -> ('a1 list -> 'a1 list -> 'a1 -> 'a1 -> ('a1, 'a2) coq_All_fold -> ('a1,
  'a2) coq_All_fold -> ('a1, 'a3) coq_All2_fold -> 'a2 -> 'a2 -> 'a3) ->
  ('a1, 'a3) coq_All2_fold

val coq_All2_fold_All_fold_mix :
  'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3) coq_All_fold
  -> ('a1, 'a3) coq_All_fold -> ('a1, ('a3, ('a3, 'a2) prod) prod)
  coq_All2_fold

val coq_All2_fold_All_fold_mix_inv :
  'a1 list -> 'a1 list -> ('a1, ('a3, ('a3, 'a2) prod) prod) coq_All2_fold ->
  (('a1, 'a2) coq_All2_fold, (('a1, 'a3) coq_All_fold, ('a1, 'a3)
  coq_All_fold) prod) prod

val coq_All_fold_All2_fold_impl :
  'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1 list -> 'a1 -> ('a1, 'a2)
  coq_All_fold -> ('a1, 'a3) coq_All2_fold -> 'a2 -> 'a3) -> ('a1, 'a3)
  coq_All2_fold

val coq_All_fold_All2_fold :
  'a1 list -> (('a1, 'a2) coq_All_fold, ('a1, 'a2) coq_All2_fold) iffT

val coq_All_remove_last : 'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All

val coq_All3_map_all :
  'a4 list -> 'a5 list -> 'a6 list -> ('a4 -> 'a1) -> ('a5 -> 'a2) -> ('a6 ->
  'a3) -> ('a4, 'a5, 'a6, 'a7) coq_All3 -> ('a1, 'a2, 'a3, 'a7) coq_All3

val coq_OnOne2All_All3 :
  'a1 list -> 'a2 list -> 'a2 list -> ('a1 -> 'a2 -> 'a2 -> 'a3 -> 'a4) ->
  ('a1 -> 'a2 -> 'a4) -> ('a2, 'a1, 'a3) coq_OnOne2All -> ('a1, 'a2, 'a2,
  'a4) coq_All3

val map_All : ('a1 -> __ -> 'a2) -> 'a1 list -> 'a2 list

type ('a, 'b, 'c, 'q) map_All_graph =
| Coq_map_All_graph_equation_1
| Coq_map_All_graph_equation_2 of 'a * 'a list
   * ('a, 'b, 'c, 'q) map_All_graph

val map_All_graph_rect :
  ('a1 -> __ -> 'a2) -> (__ -> 'a5) -> ('a1 -> 'a1 list -> __ -> ('a1, 'a2,
  'a3, 'a4) map_All_graph -> 'a5 -> 'a5) -> 'a1 list -> 'a2 list -> ('a1,
  'a2, 'a3, 'a4) map_All_graph -> 'a5

val map_All_graph_correct :
  ('a1 -> __ -> 'a2) -> 'a1 list -> ('a1, 'a2, 'a3, 'a4) map_All_graph

val map_All_elim :
  ('a1 -> __ -> 'a2) -> (__ -> 'a5) -> ('a1 -> 'a1 list -> __ -> 'a5 -> 'a5)
  -> 'a1 list -> 'a5

val coq_FunctionalElimination_map_All :
  ('a1 -> __ -> 'a2) -> (__ -> __) -> ('a1 -> 'a1 list -> __ -> __ -> __) ->
  'a1 list -> __

val coq_FunctionalInduction_map_All :
  ('a1 -> __ -> 'a2) -> ('a1 list -> __ -> 'a2 list) coq_FunctionalInduction

val coq_All_map_All :
  ('a1 -> __ -> 'a2) -> 'a1 list -> ('a3 -> 'a4 -> ('a1, __) coq_All) -> ('a1
  -> 'a3 -> __ -> __ -> 'a5) -> 'a3 -> 'a4 -> ('a2, 'a5) coq_All

val coq_All2_map2_left :
  ('a2 -> 'a3 -> 'a5) -> 'a2 list -> 'a3 list -> 'a1 list -> 'a4 list ->
  ('a2, 'a4, 'a8) coq_All2 -> ('a3, 'a1, 'a7) coq_All2 -> ('a2 -> 'a3 -> 'a1
  -> 'a4 -> 'a8 -> 'a7 -> 'a6) -> ('a5, 'a1, 'a6) coq_All2

val coq_All2_map2_left_All3 :
  ('a2 -> 'a3 -> 'a1) -> 'a2 list -> 'a3 list -> 'a1 list -> ('a2, 'a3, 'a1,
  'a4) coq_All3 -> ('a1, 'a1, 'a4) coq_All2

val coq_All3_impl :
  'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> ('a1
  -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> ('a1, 'a2, 'a3, 'a5) coq_All3

val coq_All1_map2_right_inv :
  ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a3, 'a4) coq_All2 ->
  ('a1, 'a2, 'a4) coq_All2

val coq_All1_map2_right :
  ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a4) coq_All2 ->
  ('a1, 'a3, 'a4) coq_All2

val coq_All1i_map2_right :
  nat -> ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a4)
  coq_All2i -> ('a1, 'a3, 'a4) coq_All2i

val coq_All1i_Alli_mix_left :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a3) coq_Alli -> ('a1, 'a2, 'a4)
  coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i

val coq_All_Alli_swap_iff :
  'a2 list -> 'a1 list -> nat -> (('a1, ('a2, 'a3) coq_Alli) coq_All, ('a2,
  ('a1, 'a3) coq_All) coq_Alli) iffT

val coq_All_eta3 :
  (('a1, 'a2) prod, 'a3) prod list -> (((('a1, 'a2) prod, 'a3) prod, __)
  coq_All, ((('a1, 'a2) prod, 'a3) prod, 'a4) coq_All) iffT

val coq_All2_All_swap :
  'a3 list -> 'a1 list -> 'a2 list -> ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2
  -> ('a3, ('a1, 'a2, 'a4) coq_All2) coq_All

val coq_All_All2_swap_sum :
  'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2) coq_All
  -> (__, ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2) sum

val coq_All_All2_swap :
  'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2) coq_All
  -> ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2

val coq_All2_fold_All_swap :
  'a2 list -> 'a1 list -> 'a1 list -> ('a1, ('a2, 'a3) coq_All) coq_All2_fold
  -> ('a2, ('a1, 'a3) coq_All2_fold) coq_All

val coq_All_All2_fold_swap_sum :
  'a2 list -> 'a1 list -> 'a1 list -> ('a2, ('a1, 'a3) coq_All2_fold) coq_All
  -> (__, ('a1, ('a2, 'a3) coq_All) coq_All2_fold) sum

val coq_All_All2_fold_swap :
  'a2 list -> 'a1 list -> 'a1 list -> ('a2, ('a1, 'a3) coq_All2_fold) coq_All
  -> ('a1, ('a2, 'a3) coq_All) coq_All2_fold

val coq_All2_map2_right :
  'a1 list -> 'a2 list -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2, 'a4) coq_All2 ->
  ('a1, 'a3, 'a4) coq_All2

val coq_All2i_map2_right :
  nat -> 'a1 list -> 'a2 list -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2, 'a4)
  coq_All2i -> ('a1, 'a3, 'a4) coq_All2i

val coq_All2_map2_right_inv :
  ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a3, 'a4) coq_All2 ->
  ('a1, 'a2, 'a4) coq_All2

val coq_All2i_Alli_mix_left :
  nat -> 'a1 list -> 'a2 list -> ('a1, 'a3) coq_Alli -> ('a1, 'a2, 'a4)
  coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i
