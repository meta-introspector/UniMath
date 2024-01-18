open All_Forall
open Ast
open BasicAst
open CRelationClasses
open Classes
open Datatypes
open Induction
open Kernames
open Nat
open PrimFloat
open PrimInt63
open Signature
open Universes
open Config

type __ = Obj.t

val global_variance_gen :
  (kername -> Env.global_decl option) -> global_reference -> nat ->
  Variance.t list option

type ('eq_term, 'leq_term) compare_decls =
| Coq_compare_vass of name binder_annot * term * name binder_annot * 
   term * 'leq_term
| Coq_compare_vdef of name binder_annot * term * term * name binder_annot
   * term * term * 'eq_term * 'leq_term

val compare_decls_rect :
  (name binder_annot -> term -> name binder_annot -> term -> __ -> 'a2 ->
  'a3) -> (name binder_annot -> term -> term -> name binder_annot -> term ->
  term -> __ -> 'a1 -> 'a2 -> 'a3) -> term context_decl -> term context_decl
  -> ('a1, 'a2) compare_decls -> 'a3

val compare_decls_rec :
  (name binder_annot -> term -> name binder_annot -> term -> __ -> 'a2 ->
  'a3) -> (name binder_annot -> term -> term -> name binder_annot -> term ->
  term -> __ -> 'a1 -> 'a2 -> 'a3) -> term context_decl -> term context_decl
  -> ('a1, 'a2) compare_decls -> 'a3

type ('eq_term, 'leq_term) compare_decls_sig =
  ('eq_term, 'leq_term) compare_decls

val compare_decls_sig_pack :
  term context_decl -> term context_decl -> ('a1, 'a2) compare_decls -> (term
  context_decl * term context_decl) * ('a1, 'a2) compare_decls

val compare_decls_Signature :
  term context_decl -> term context_decl -> (('a1, 'a2) compare_decls, term
  context_decl * term context_decl, ('a1, 'a2) compare_decls_sig)
  coq_Signature

val coq_NoConfusionPackage_compare_decls :
  ((term context_decl * term context_decl) * ('a1, 'a2) compare_decls)
  coq_NoConfusionPackage

val alpha_eq_subst_context :
  term context_decl list -> term context_decl list -> term list -> nat ->
  (term context_decl, term context_decl, (__, __) compare_decls) coq_All2 ->
  (term context_decl, term context_decl, (__, __) compare_decls) coq_All2

type eq_term_upto_univ_napp =
| Coq_eq_Rel of nat
| Coq_eq_Evar of nat * term list * term list
   * (term, term, eq_term_upto_univ_napp) coq_All2
| Coq_eq_Var of ident
| Coq_eq_Sort of Universe.t * Universe.t
| Coq_eq_App of term * term * term list * term list * eq_term_upto_univ_napp
   * (term, term, eq_term_upto_univ_napp) coq_All2
| Coq_eq_Const of kername * Level.t list * Level.t list
| Coq_eq_Ind of inductive * Level.t list * Level.t list
| Coq_eq_Construct of inductive * nat * Level.t list * Level.t list
| Coq_eq_Lambda of name binder_annot * name binder_annot * term * term * 
   term * term * eq_term_upto_univ_napp * eq_term_upto_univ_napp
| Coq_eq_Prod of name binder_annot * name binder_annot * term * term * 
   term * term * eq_term_upto_univ_napp * eq_term_upto_univ_napp
| Coq_eq_LetIn of name binder_annot * name binder_annot * term * term * 
   term * term * term * term * eq_term_upto_univ_napp
   * eq_term_upto_univ_napp * eq_term_upto_univ_napp
| Coq_eq_Case of case_info * term predicate * term predicate * term * 
   term * term branch list * term branch list
   * (term, term, eq_term_upto_univ_napp) coq_All2 * eq_term_upto_univ_napp
   * (name binder_annot, name binder_annot, __) coq_All2
   * eq_term_upto_univ_napp
   * (term branch, term branch, ((name binder_annot, name binder_annot, __)
     coq_All2, eq_term_upto_univ_napp) prod) coq_All2
| Coq_eq_Proj of projection * term * term * eq_term_upto_univ_napp
| Coq_eq_Fix of term def list * term def list * nat
   * (term def, term def, (((eq_term_upto_univ_napp, eq_term_upto_univ_napp)
     prod, __) prod, __) prod) coq_All2
| Coq_eq_CoFix of term def list * term def list * nat
   * (term def, term def, (((eq_term_upto_univ_napp, eq_term_upto_univ_napp)
     prod, __) prod, __) prod) coq_All2
| Coq_eq_Cast of term * cast_kind * term * term * cast_kind * term
   * eq_term_upto_univ_napp * eq_term_upto_univ_napp
| Coq_eq_Int of int
| Coq_eq_Float of float

val eq_term_upto_univ_napp_rect :
  Env.global_env -> (__ -> nat -> nat -> 'a1) -> (__ -> nat -> nat -> term
  list -> term list -> (term, term, eq_term_upto_univ_napp) coq_All2 -> 'a1)
  -> (__ -> nat -> ident -> 'a1) -> (__ -> nat -> Universe.t -> Universe.t ->
  __ -> 'a1) -> (__ -> nat -> term -> term -> term list -> term list ->
  eq_term_upto_univ_napp -> 'a1 -> (term, term, eq_term_upto_univ_napp)
  coq_All2 -> 'a1) -> (__ -> nat -> kername -> Level.t list -> Level.t list
  -> __ -> 'a1) -> (__ -> nat -> inductive -> Level.t list -> Level.t list ->
  __ -> 'a1) -> (__ -> nat -> inductive -> nat -> Level.t list -> Level.t
  list -> __ -> 'a1) -> (__ -> nat -> name binder_annot -> name binder_annot
  -> term -> term -> term -> term -> __ -> eq_term_upto_univ_napp -> 'a1 ->
  eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> name binder_annot ->
  name binder_annot -> term -> term -> term -> term -> __ ->
  eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 -> 'a1) ->
  (__ -> nat -> name binder_annot -> name binder_annot -> term -> term ->
  term -> term -> term -> term -> __ -> eq_term_upto_univ_napp -> 'a1 ->
  eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 -> 'a1) ->
  (__ -> nat -> case_info -> term predicate -> term predicate -> term -> term
  -> term branch list -> term branch list -> (term, term,
  eq_term_upto_univ_napp) coq_All2 -> __ -> eq_term_upto_univ_napp -> 'a1 ->
  (name binder_annot, name binder_annot, __) coq_All2 ->
  eq_term_upto_univ_napp -> 'a1 -> (term branch, term branch, ((name
  binder_annot, name binder_annot, __) coq_All2, eq_term_upto_univ_napp)
  prod) coq_All2 -> 'a1) -> (__ -> nat -> projection -> term -> term ->
  eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> term def list ->
  term def list -> nat -> (term def, term def, (((eq_term_upto_univ_napp,
  eq_term_upto_univ_napp) prod, __) prod, __) prod) coq_All2 -> 'a1) -> (__
  -> nat -> term def list -> term def list -> nat -> (term def, term def,
  (((eq_term_upto_univ_napp, eq_term_upto_univ_napp) prod, __) prod, __)
  prod) coq_All2 -> 'a1) -> (__ -> nat -> term -> cast_kind -> term -> term
  -> cast_kind -> term -> eq_term_upto_univ_napp -> 'a1 -> __ ->
  eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> int -> 'a1) -> (__
  -> nat -> float -> 'a1) -> nat -> term -> term -> eq_term_upto_univ_napp ->
  'a1

val eq_term_upto_univ_napp_rec :
  Env.global_env -> (__ -> nat -> nat -> 'a1) -> (__ -> nat -> nat -> term
  list -> term list -> (term, term, eq_term_upto_univ_napp) coq_All2 -> 'a1)
  -> (__ -> nat -> ident -> 'a1) -> (__ -> nat -> Universe.t -> Universe.t ->
  __ -> 'a1) -> (__ -> nat -> term -> term -> term list -> term list ->
  eq_term_upto_univ_napp -> 'a1 -> (term, term, eq_term_upto_univ_napp)
  coq_All2 -> 'a1) -> (__ -> nat -> kername -> Level.t list -> Level.t list
  -> __ -> 'a1) -> (__ -> nat -> inductive -> Level.t list -> Level.t list ->
  __ -> 'a1) -> (__ -> nat -> inductive -> nat -> Level.t list -> Level.t
  list -> __ -> 'a1) -> (__ -> nat -> name binder_annot -> name binder_annot
  -> term -> term -> term -> term -> __ -> eq_term_upto_univ_napp -> 'a1 ->
  eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> name binder_annot ->
  name binder_annot -> term -> term -> term -> term -> __ ->
  eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 -> 'a1) ->
  (__ -> nat -> name binder_annot -> name binder_annot -> term -> term ->
  term -> term -> term -> term -> __ -> eq_term_upto_univ_napp -> 'a1 ->
  eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 -> 'a1) ->
  (__ -> nat -> case_info -> term predicate -> term predicate -> term -> term
  -> term branch list -> term branch list -> (term, term,
  eq_term_upto_univ_napp) coq_All2 -> __ -> eq_term_upto_univ_napp -> 'a1 ->
  (name binder_annot, name binder_annot, __) coq_All2 ->
  eq_term_upto_univ_napp -> 'a1 -> (term branch, term branch, ((name
  binder_annot, name binder_annot, __) coq_All2, eq_term_upto_univ_napp)
  prod) coq_All2 -> 'a1) -> (__ -> nat -> projection -> term -> term ->
  eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> term def list ->
  term def list -> nat -> (term def, term def, (((eq_term_upto_univ_napp,
  eq_term_upto_univ_napp) prod, __) prod, __) prod) coq_All2 -> 'a1) -> (__
  -> nat -> term def list -> term def list -> nat -> (term def, term def,
  (((eq_term_upto_univ_napp, eq_term_upto_univ_napp) prod, __) prod, __)
  prod) coq_All2 -> 'a1) -> (__ -> nat -> term -> cast_kind -> term -> term
  -> cast_kind -> term -> eq_term_upto_univ_napp -> 'a1 -> __ ->
  eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> int -> 'a1) -> (__
  -> nat -> float -> 'a1) -> nat -> term -> term -> eq_term_upto_univ_napp ->
  'a1

type compare_term = eq_term_upto_univ_napp

val eq_binder_annots_refl :
  ('a1 binder_annot list, ('a1 binder_annot, 'a1 binder_annot, __) coq_All2)
  coq_Equivalence

val eq_term_upto_univ_refl :
  Env.global_env -> nat -> term -> eq_term_upto_univ_napp

val eq_term_refl :
  checker_flags -> Env.global_env -> ConstraintSet.t -> term -> compare_term

val leq_term_refl :
  checker_flags -> Env.global_env -> ConstraintSet.t -> term -> compare_term

val eq_term_upto_univ_morphism0 :
  Env.global_env -> term -> term -> nat -> eq_term_upto_univ_napp ->
  eq_term_upto_univ_napp

val eq_term_upto_univ_morphism :
  Env.global_env -> term -> term -> nat -> eq_term_upto_univ_napp ->
  eq_term_upto_univ_napp

val eq_term_upto_univ_impl :
  Env.global_env -> nat -> nat -> (term, eq_term_upto_univ_napp,
  eq_term_upto_univ_napp) subrelation

val eq_term_leq_term :
  checker_flags -> Env.global_env -> ConstraintSet.t -> term -> term ->
  compare_term -> compare_term

val eq_term_upto_univ_mkApps :
  checker_flags -> Env.global_env -> nat -> term -> term list -> term -> term
  list -> eq_term_upto_univ_napp -> (term, term, eq_term_upto_univ_napp)
  coq_All2 -> eq_term_upto_univ_napp

val leq_term_mkApps :
  checker_flags -> Env.global_env -> ConstraintSet.t -> term -> term list ->
  term -> term list -> compare_term -> (term, term, compare_term) coq_All2 ->
  compare_term
