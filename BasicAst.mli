open All_Forall
open BinInt
open BinNums
open Byte
open CRelationClasses
open Classes
open Datatypes
open EqDecInstances
open Kernames
open List
open MCList
open MCOption
open MCReflect
open MCString
open Nat
open ReflectEq
open SpecFloat
open Specif
open Bytestring

type __ = Obj.t

type name =
| Coq_nAnon
| Coq_nNamed of ident

val name_rect : 'a1 -> (ident -> 'a1) -> name -> 'a1

val name_rec : 'a1 -> (ident -> 'a1) -> name -> 'a1

val coq_NoConfusionPackage_name : name coq_NoConfusionPackage

val name_eqdec : name -> name -> name dec_eq

val name_EqDec : name coq_EqDec

type relevance =
| Relevant
| Irrelevant

val relevance_rect : 'a1 -> 'a1 -> relevance -> 'a1

val relevance_rec : 'a1 -> 'a1 -> relevance -> 'a1

val coq_NoConfusionPackage_relevance : relevance coq_NoConfusionPackage

val relevance_eqdec : relevance -> relevance -> relevance dec_eq

val relevance_EqDec : relevance coq_EqDec

type 'a binder_annot = { binder_name : 'a; binder_relevance : relevance }

val binder_name : 'a1 binder_annot -> 'a1

val binder_relevance : 'a1 binder_annot -> relevance

val coq_NoConfusionPackage_binder_annot :
  'a1 binder_annot coq_NoConfusionPackage

val eqdec_binder_annot : 'a1 coq_EqDec -> 'a1 binder_annot coq_EqDec

val map_binder_annot : ('a1 -> 'a2) -> 'a1 binder_annot -> 'a2 binder_annot

type aname = name binder_annot

val anqme_eqdec : aname coq_EqDec

val eqb_binder_annot : 'a1 binder_annot -> 'a1 binder_annot -> bool

val string_of_name : name -> String.t

val string_of_relevance : relevance -> String.t

type cast_kind =
| VmCast
| NativeCast
| Cast

val cast_kind_rect : 'a1 -> 'a1 -> 'a1 -> cast_kind -> 'a1

val cast_kind_rec : 'a1 -> 'a1 -> 'a1 -> cast_kind -> 'a1

val coq_NoConfusionPackage_cast_kind : cast_kind coq_NoConfusionPackage

val cast_kind_eqdec : cast_kind -> cast_kind -> cast_kind dec_eq

val cast_kind_EqDec : cast_kind coq_EqDec

type case_info = { ci_ind : inductive; ci_npar : nat; ci_relevance : relevance }

val ci_ind : case_info -> inductive

val ci_npar : case_info -> nat

val ci_relevance : case_info -> relevance

val coq_NoConfusionPackage_case_info : case_info coq_NoConfusionPackage

val case_info_eqdec : case_info -> case_info -> case_info dec_eq

val case_info_EqDec : case_info coq_EqDec

val string_of_case_info : case_info -> String.t

type recursivity_kind =
| Finite
| CoFinite
| BiFinite

val recursivity_kind_rect : 'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1

val recursivity_kind_rec : 'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1

val coq_NoConfusionPackage_recursivity_kind :
  recursivity_kind coq_NoConfusionPackage

val recursivity_kind_eqdec :
  recursivity_kind -> recursivity_kind -> recursivity_kind dec_eq

val recursivity_kind_EqDec : recursivity_kind coq_EqDec

type conv_pb =
| Conv
| Cumul

val conv_pb_rect : 'a1 -> 'a1 -> conv_pb -> 'a1

val conv_pb_rec : 'a1 -> 'a1 -> conv_pb -> 'a1

val coq_NoConfusionPackage_conv_pb : conv_pb coq_NoConfusionPackage

val conv_pb_eqdec : conv_pb -> conv_pb -> conv_pb dec_eq

val conv_pb_EqDec : conv_pb coq_EqDec

val conv_pb_leqb : conv_pb -> conv_pb -> bool

val fresh_evar_id : nat

type 'term def = { dname : aname; dtype : 'term; dbody : 'term; rarg : nat }

val dname : 'a1 def -> aname

val dtype : 'a1 def -> 'a1

val dbody : 'a1 def -> 'a1

val rarg : 'a1 def -> nat

val coq_NoConfusionPackage_def : 'a1 def coq_NoConfusionPackage

val def_eq_dec : 'a1 coq_EqDec -> 'a1 def coq_EqDec

val string_of_def : ('a1 -> String.t) -> 'a1 def -> String.t

val print_def : ('a1 -> String.t) -> ('a1 -> String.t) -> 'a1 def -> String.t

val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def

type 'term mfixpoint = 'term def list

val test_def : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 def -> bool

type ('a, 'p, 'x) tFixProp = ('a def, ('p, 'x) prod) coq_All

type 'term typ_or_sort_ =
| Typ of 'term
| Sort

val typ_or_sort_map : ('a1 -> 'a2) -> 'a1 typ_or_sort_ -> 'a2 typ_or_sort_

val typ_or_sort_default : ('a1 -> 'a2) -> 'a1 typ_or_sort_ -> 'a2 -> 'a2

type 'term context_decl = { decl_name : aname; decl_body : 'term option;
                            decl_type : 'term }

val decl_name : 'a1 context_decl -> aname

val decl_body : 'a1 context_decl -> 'a1 option

val decl_type : 'a1 context_decl -> 'a1

val coq_NoConfusionPackage_context_decl :
  'a1 context_decl coq_NoConfusionPackage

val map_decl : ('a1 -> 'a2) -> 'a1 context_decl -> 'a2 context_decl

val map_context :
  ('a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list

val test_decl : ('a1 -> bool) -> 'a1 context_decl -> bool

val snoc : 'a1 list -> 'a1 -> 'a1 list

type ('a, 'p) ondecl = ('p, __) prod

val mapi_context :
  (nat -> 'a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list

val test_context : ('a1 -> bool) -> 'a1 context_decl list -> bool

val test_context_k :
  (nat -> 'a1 -> bool) -> nat -> 'a1 context_decl list -> bool

type ('term, 'p) onctx_k = ('term context_decl, ('term, 'p) ondecl) coq_Alli

val ondeclP :
  ('a1 -> bool) -> 'a1 context_decl -> ('a1 -> 'a2 reflectT) -> ('a1, 'a2)
  ondecl reflectT

val onctxP :
  ('a1 -> bool) -> 'a1 context_decl list -> ('a1 context_decl, ('a1, __)
  ondecl) coq_All reflectT

val fold_context_k :
  (nat -> 'a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list

val mapi_context_In :
  'a1 context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1
  context_decl) -> 'a1 context_decl list

type 'term mapi_context_In_graph =
| Coq_mapi_context_In_graph_equation_1 of (nat -> 'term context_decl -> __ ->
                                          'term context_decl)
| Coq_mapi_context_In_graph_equation_2 of 'term context_decl
   * 'term context_decl list
   * (nat -> 'term context_decl -> __ -> 'term context_decl)
   * 'term mapi_context_In_graph

val mapi_context_In_graph_rect :
  ((nat -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a2) -> ('a1
  context_decl -> 'a1 context_decl list -> (nat -> 'a1 context_decl -> __ ->
  'a1 context_decl) -> 'a1 mapi_context_In_graph -> 'a2 -> 'a2) -> 'a1
  context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1 context_decl) ->
  'a1 context_decl list -> 'a1 mapi_context_In_graph -> 'a2

val mapi_context_In_graph_correct :
  'a1 context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1
  context_decl) -> 'a1 mapi_context_In_graph

val mapi_context_In_elim :
  ((nat -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a2) -> ('a1
  context_decl -> 'a1 context_decl list -> (nat -> 'a1 context_decl -> __ ->
  'a1 context_decl) -> 'a2 -> 'a2) -> 'a1 context_decl list -> (nat -> 'a1
  context_decl -> __ -> 'a1 context_decl) -> 'a2

val coq_FunctionalElimination_mapi_context_In :
  ((nat -> 'a1 context_decl -> __ -> 'a1 context_decl) -> __) -> ('a1
  context_decl -> 'a1 context_decl list -> (nat -> 'a1 context_decl -> __ ->
  'a1 context_decl) -> __ -> __) -> 'a1 context_decl list -> (nat -> 'a1
  context_decl -> __ -> 'a1 context_decl) -> __

val coq_FunctionalInduction_mapi_context_In :
  ('a1 context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1
  context_decl) -> 'a1 context_decl list) coq_FunctionalInduction

val fold_context_In :
  'a1 context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __
  -> 'a1 context_decl) -> 'a1 context_decl list

type 'term fold_context_In_graph =
| Coq_fold_context_In_graph_equation_1 of ('term context_decl list -> 'term
                                          context_decl -> __ -> 'term
                                          context_decl)
| Coq_fold_context_In_graph_equation_2 of 'term context_decl
   * 'term context_decl list
   * ('term context_decl list -> 'term context_decl -> __ -> 'term
     context_decl) * 'term fold_context_In_graph

val fold_context_In_graph_rect :
  (('a1 context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) ->
  'a2) -> ('a1 context_decl -> 'a1 context_decl list -> ('a1 context_decl
  list -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a1
  fold_context_In_graph -> 'a2 -> 'a2) -> 'a1 context_decl list -> ('a1
  context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a1
  context_decl list -> 'a1 fold_context_In_graph -> 'a2

val fold_context_In_graph_correct :
  'a1 context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __
  -> 'a1 context_decl) -> 'a1 fold_context_In_graph

val fold_context_In_elim :
  (('a1 context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) ->
  'a2) -> ('a1 context_decl -> 'a1 context_decl list -> ('a1 context_decl
  list -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a2 -> 'a2) -> 'a1
  context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __ ->
  'a1 context_decl) -> 'a2

val coq_FunctionalElimination_fold_context_In :
  (('a1 context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) ->
  __) -> ('a1 context_decl -> 'a1 context_decl list -> ('a1 context_decl list
  -> 'a1 context_decl -> __ -> 'a1 context_decl) -> __ -> __) -> 'a1
  context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __ ->
  'a1 context_decl) -> __

val coq_FunctionalInduction_fold_context_In :
  ('a1 context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __
  -> 'a1 context_decl) -> 'a1 context_decl list) coq_FunctionalInduction

val fold_context :
  ('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
  context_decl list -> 'a1 context_decl list

type 'term fold_context_graph =
| Coq_fold_context_graph_equation_1 of ('term context_decl list -> 'term
                                       context_decl -> 'term context_decl)
| Coq_fold_context_graph_equation_2 of ('term context_decl list -> 'term
                                       context_decl -> 'term context_decl)
   * 'term context_decl * 'term context_decl list * 'term fold_context_graph

val fold_context_graph_rect :
  (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a2) ->
  (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
  context_decl -> 'a1 context_decl list -> 'a1 fold_context_graph -> 'a2 ->
  'a2) -> ('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) ->
  'a1 context_decl list -> 'a1 context_decl list -> 'a1 fold_context_graph ->
  'a2

val fold_context_graph_correct :
  ('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
  context_decl list -> 'a1 fold_context_graph

val fold_context_elim :
  (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a2) ->
  (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
  context_decl -> 'a1 context_decl list -> 'a2 -> 'a2) -> ('a1 context_decl
  list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1 context_decl list ->
  'a2

val coq_FunctionalElimination_fold_context :
  (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> __) ->
  (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
  context_decl -> 'a1 context_decl list -> __ -> __) -> ('a1 context_decl
  list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1 context_decl list -> __

val coq_FunctionalInduction_fold_context :
  (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
  context_decl list -> 'a1 context_decl list) coq_FunctionalInduction

val forget_types : 'a1 context_decl list -> aname list

val coq_All2_fold_impl_onctx :
  'a1 context_decl list -> 'a1 context_decl list -> ('a1 context_decl, ('a1,
  'a4) ondecl) coq_All -> ('a1 context_decl, 'a2) coq_All2_fold -> ('a1
  context_decl list -> 'a1 context_decl list -> 'a1 context_decl -> 'a1
  context_decl -> ('a1 context_decl, 'a2) coq_All2_fold -> 'a2 -> ('a1, 'a4)
  ondecl -> 'a3) -> ('a1 context_decl, 'a3) coq_All2_fold

val coq_All2_fold_mapi :
  'a1 context_decl list -> 'a1 context_decl list -> (nat -> 'a1 -> 'a1) ->
  (nat -> 'a1 -> 'a1) -> (('a1 context_decl, 'a2) coq_All2_fold, ('a1
  context_decl, 'a2) coq_All2_fold) iffT

val coq_All2_fold_map :
  'a1 context_decl list -> 'a1 context_decl list -> ('a1 -> 'a1) -> ('a1 ->
  'a1) -> (('a1 context_decl, 'a2) coq_All2_fold, ('a1 context_decl, 'a2)
  coq_All2_fold) iffT

val coq_All2_fold_cst_map :
  'a1 context_decl list -> 'a1 context_decl list -> ('a1 context_decl -> 'a1
  context_decl) -> ('a1 context_decl -> 'a1 context_decl) -> (('a1
  context_decl, 'a2) coq_All2_fold, ('a1 context_decl, 'a2) coq_All2_fold)
  iffT

val uint_size : nat

val uint_wB : coq_Z

type uint63_model = coq_Z

val string_of_uint63_model : uint63_model -> String.t

val prec : coq_Z

val emax : coq_Z

type float64_model = spec_float
