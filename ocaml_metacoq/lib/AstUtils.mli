open All_Forall
open Ast
open BasicAst
open Byte
open Datatypes
open Kernames
open List
open MCString
open Nat
open Primitive
open ReflectEq
open Universes
open Bytestring
open Monad_utils

type __ = Obj.t

module Coq_string_of_term_tree :
 sig
  val string_of_predicate : ('a1 -> Tree.t) -> 'a1 predicate -> Tree.t

  val string_of_branch : (term -> Tree.t) -> term branch -> Tree.t

  val string_of_def : ('a1 -> Tree.t) -> 'a1 def -> Tree.t

  val string_of_term : term -> Tree.t
 end

val string_of_term : term -> String.t

val decompose_app : term -> (term, term list) prod

type mkApps_spec =
| Coq_mkApps_intro of term * term list * nat

val mkApps_spec_rect :
  (term -> term list -> nat -> __ -> 'a1) -> term -> term list -> term ->
  term list -> term -> mkApps_spec -> 'a1

val mkApps_spec_rec :
  (term -> term list -> nat -> __ -> 'a1) -> term -> term list -> term ->
  term list -> term -> mkApps_spec -> 'a1

val is_empty : 'a1 list -> bool

val decompose_prod : term -> ((aname list, term list) prod, term) prod

val remove_arity : nat -> term -> term

val lookup_mind_decl :
  kername -> Env.global_declarations -> Env.mutual_inductive_body option

val mind_body_to_entry : Env.mutual_inductive_body -> mutual_inductive_entry

val strip_casts : term -> term

val decompose_prod_assum : Env.context -> term -> (Env.context, term) prod

val strip_outer_cast : term -> term

val decompose_prod_n_assum :
  Env.context -> nat -> term -> (Env.context, term) prod option

val decompose_lam_n_assum :
  Env.context -> nat -> term -> (Env.context, term) prod option

val is_ind_app_head : term -> bool

val isConstruct_app : term -> bool

val lookup_minductive :
  Env.global_env -> kername -> Env.mutual_inductive_body option

val lookup_inductive :
  Env.global_env -> inductive -> (Env.mutual_inductive_body,
  Env.one_inductive_body) prod option

val destInd : term -> (inductive, Instance.t) prod option

val forget_types : 'a1 context_decl list -> aname list

val mkCase_old :
  Env.global_env -> case_info -> term -> term -> (nat, term) prod list ->
  term option

val default_sort_family : Universe.t -> allowed_eliminations

val default_relevance : Universe.t -> relevance

val make_constructor_body :
  ident -> nat -> Env.context -> Env.context -> term list ->
  Env.constructor_body

val make_inductive_body :
  ident -> Env.context -> Env.context -> Universe.t -> Env.constructor_body
  list -> Env.one_inductive_body

type ('a, 'p) tCaseBrsType = ('a branch, 'p) coq_All

type ('a, 'p, 'x) tFixType = ('a def, ('p, 'x) prod) coq_All
