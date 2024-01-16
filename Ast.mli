open All_Forall
open BasicAst
open Byte
open CRelationClasses
open Classes
open Datatypes
open EnvironmentTyping
open EqDecInstances
open Kernames
open List
open MCList
open MCProd
open Nat
open PrimFloat
open PrimInt63
open Primitive
open ReflectEq
open Signature
open Specif
open Universes
open Bytestring
open Config

type __ = Obj.t

type 'term predicate = { puinst : Instance.t; pparams : 'term list;
                         pcontext : aname list; preturn : 'term }

val puinst : 'a1 predicate -> Instance.t

val pparams : 'a1 predicate -> 'a1 list

val pcontext : 'a1 predicate -> aname list

val preturn : 'a1 predicate -> 'a1

val coq_NoConfusionPackage_predicate : 'a1 predicate coq_NoConfusionPackage

val predicate_eq_dec : 'a1 coq_EqDec -> 'a1 predicate coq_EqDec

val string_of_predicate : ('a1 -> String.t) -> 'a1 predicate -> String.t

val test_predicate :
  (Instance.t -> bool) -> ('a1 -> bool) -> ('a1 -> bool) -> 'a1 predicate ->
  bool

val eqb_predicate :
  (Instance.t -> Instance.t -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 predicate
  -> 'a1 predicate -> bool

val map_predicate :
  (Instance.t -> Instance.t) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 predicate
  -> 'a2 predicate

type ('term, 'pparams, 'preturn) tCasePredProp =
  (('term, 'pparams) coq_All, 'preturn) prod

val map_predicate_k :
  (Instance.t -> Instance.t) -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 predicate
  -> 'a1 predicate

val test_predicate_k :
  (Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1 predicate -> bool

type 'term branch = { bcontext : aname list; bbody : 'term }

val bcontext : 'a1 branch -> aname list

val bbody : 'a1 branch -> 'a1

val coq_NoConfusionPackage_branch : 'a1 branch coq_NoConfusionPackage

val branch_eq_dec : 'a1 coq_EqDec -> 'a1 branch coq_EqDec

val string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t

val pretty_string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t

val test_branch : ('a1 -> bool) -> 'a1 branch -> bool

val map_branch : ('a1 -> 'a2) -> 'a1 branch -> 'a2 branch

val map_branches : ('a1 -> 'a2) -> 'a1 branch list -> 'a2 branch list

type ('a, 'p) tCaseBrsProp = ('a branch, 'p) coq_All

module Coq__1 : sig
 type term =
 | Coq_tRel of nat
 | Coq_tVar of ident
 | Coq_tEvar of nat * term list
 | Coq_tSort of Universe.t
 | Coq_tCast of term * cast_kind * term
 | Coq_tProd of aname * term * term
 | Coq_tLambda of aname * term * term
 | Coq_tLetIn of aname * term * term * term
 | Coq_tApp of term * term list
 | Coq_tConst of kername * Instance.t
 | Coq_tInd of inductive * Instance.t
 | Coq_tConstruct of inductive * nat * Instance.t
 | Coq_tCase of case_info * term predicate * term * term branch list
 | Coq_tProj of projection * term
 | Coq_tFix of term mfixpoint * nat
 | Coq_tCoFix of term mfixpoint * nat
 | Coq_tInt of int
 | Coq_tFloat of float
end
include module type of struct include Coq__1 end

val term_rect :
  (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (Universe.t
  -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 -> 'a1) -> (aname ->
  term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1
  -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> term -> 'a1 -> 'a1) ->
  (term -> 'a1 -> term list -> 'a1) -> (kername -> Instance.t -> 'a1) ->
  (inductive -> Instance.t -> 'a1) -> (inductive -> nat -> Instance.t -> 'a1)
  -> (case_info -> term predicate -> term -> 'a1 -> term branch list -> 'a1)
  -> (projection -> term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> 'a1) ->
  (term mfixpoint -> nat -> 'a1) -> (int -> 'a1) -> (float -> 'a1) -> term ->
  'a1

val term_rec :
  (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) -> (Universe.t
  -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 -> 'a1) -> (aname ->
  term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1
  -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> term -> 'a1 -> 'a1) ->
  (term -> 'a1 -> term list -> 'a1) -> (kername -> Instance.t -> 'a1) ->
  (inductive -> Instance.t -> 'a1) -> (inductive -> nat -> Instance.t -> 'a1)
  -> (case_info -> term predicate -> term -> 'a1 -> term branch list -> 'a1)
  -> (projection -> term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> 'a1) ->
  (term mfixpoint -> nat -> 'a1) -> (int -> 'a1) -> (float -> 'a1) -> term ->
  'a1

val hole : term

val mkApps : term -> term list -> term

val lift : nat -> nat -> term -> term

val subst : term list -> nat -> term -> term

val subst1 : term -> nat -> term -> term

val closedn : nat -> term -> bool

val noccur_between : nat -> nat -> term -> bool

val subst_instance_constr : term coq_UnivSubst

val closedu : nat -> term -> bool

module TemplateTerm :
 sig
  type term = Coq__1.term

  val tRel : nat -> Coq__1.term

  val tSort : Universe.t -> Coq__1.term

  val tProd : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tLambda : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tLetIn :
    aname -> Coq__1.term -> Coq__1.term -> Coq__1.term -> Coq__1.term

  val tInd : inductive -> Instance.t -> Coq__1.term

  val tProj : projection -> Coq__1.term -> Coq__1.term

  val mkApps : Coq__1.term -> Coq__1.term list -> Coq__1.term

  val lift : nat -> nat -> Coq__1.term -> Coq__1.term

  val subst : Coq__1.term list -> nat -> Coq__1.term -> Coq__1.term

  val closedn : nat -> Coq__1.term -> bool

  val noccur_between : nat -> nat -> Coq__1.term -> bool

  val subst_instance_constr : Instance.t -> Coq__1.term -> Coq__1.term
 end

module Env :
 sig
  type typ_or_sort = term typ_or_sort_

  val vass : aname -> term -> term context_decl

  val vdef : aname -> term -> term -> term context_decl

  type context = term context_decl list

  val lift_decl : nat -> nat -> term context_decl -> term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : term list -> nat -> context -> context

  val subst_decl : term list -> nat -> term context_decl -> term context_decl

  val subst_telescope : term list -> nat -> context -> context

  val subst_instance_decl : term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> term context_decl -> term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> term list

  val expand_lets_k : context -> nat -> term -> term

  val expand_lets : context -> term -> term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : term list; cstr_type : term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> term list

  val cstr_type : constructor_body -> term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> term

  val map_constructor_body :
    nat -> nat -> (nat -> term -> term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> term -> term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> term -> term) -> one_inductive_body ->
    one_inductive_body

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  val ind_finite : mutual_inductive_body -> recursivity_kind

  val ind_npars : mutual_inductive_body -> nat

  val ind_params : mutual_inductive_body -> context

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  val ind_universes : mutual_inductive_body -> universes_decl

  val ind_variance : mutual_inductive_body -> Variance.t list option

  type constant_body = { cst_type : term; cst_body : term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> term

  val cst_body : constant_body -> term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (term -> term) -> constant_body -> constant_body

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
    -> 'a1

  val coq_NoConfusionPackage_global_decl : global_decl coq_NoConfusionPackage

  type global_declarations = (kername, global_decl) prod list

  type global_env = { universes : ContextSet.t;
                      declarations : global_declarations;
                      retroknowledge : Environment.Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Environment.Retroknowledge.t

  val empty_global_env : global_env

  val add_global_decl :
    global_env -> (kername, global_decl) prod -> global_env

  val set_declarations : global_env -> global_declarations -> global_env

  val lookup_global : global_declarations -> kername -> global_decl option

  val lookup_env : global_env -> kername -> global_decl option

  val lookup_globals : global_declarations -> kername -> global_decl list

  val lookup_envs : global_env -> kername -> global_decl list

  type extends = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_decls = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_strictly_on_decls =
    (__, ((kername, global_decl) prod list, __) sigT, __) and3

  type strictly_extends_decls =
    (__, ((kername, global_decl) prod list, __) sigT, __) and3

  val strictly_extends_decls_extends_part_globals :
    (kername, global_decl) prod list -> (kername, global_decl) prod list ->
    ((kername, global_decl) prod list, __) sigT -> kername -> (global_decl
    list, __) sigT

  val strictly_extends_decls_extends_part :
    global_env -> global_env -> ((kername, global_decl) prod list, __) sigT
    -> kername -> (global_decl list, __) sigT

  val strictly_extends_decls_extends_decls :
    global_env -> global_env -> strictly_extends_decls -> extends_decls

  val strictly_extends_decls_extends_strictly_on_decls :
    global_env -> global_env -> strictly_extends_decls ->
    extends_strictly_on_decls

  val extends_decls_extends :
    global_env -> global_env -> extends_decls -> extends

  val extends_strictly_on_decls_extends :
    global_env -> global_env -> extends_strictly_on_decls -> extends

  val strictly_extends_decls_extends_decls_subrel :
    (global_env, strictly_extends_decls, extends_decls) subrelation

  val strictly_extends_decls_extends_strictly_on_decls_subrel :
    (global_env, strictly_extends_decls, extends_strictly_on_decls)
    subrelation

  val extends_decls_extends_subrel :
    (global_env, extends_decls, extends) subrelation

  val extends_strictly_on_decls_extends_subrel :
    (global_env, extends_strictly_on_decls, extends) subrelation

  val strictly_extends_decls_extends_subrel :
    (global_env, strictly_extends_decls, extends) subrelation

  val strictly_extends_decls_refl :
    (global_env, strictly_extends_decls) coq_Reflexive

  val extends_decls_refl : (global_env, extends_decls) coq_Reflexive

  val extends_strictly_on_decls_refl :
    (global_env, extends_strictly_on_decls) coq_Reflexive

  val extends_refl : (global_env, extends) coq_Reflexive

  val extends_decls_part_globals_refl :
    global_declarations -> kername -> (global_decl list, __) sigT

  val extends_decls_part_refl :
    global_env -> kername -> (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_refl :
    global_declarations -> ((kername, global_decl) prod list, __) sigT

  val strictly_extends_decls_part_refl :
    global_env -> ((kername, global_decl) prod list, __) sigT

  val extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    (kername -> (global_decl list, __) sigT) -> (kername -> (global_decl
    list, __) sigT) -> kername -> (global_decl list, __) sigT

  val extends_decls_part_trans :
    global_env -> global_env -> global_env -> (kername -> (global_decl list,
    __) sigT) -> (kername -> (global_decl list, __) sigT) -> kername ->
    (global_decl list, __) sigT

  val strictly_extends_decls_part_globals_trans :
    global_declarations -> global_declarations -> global_declarations ->
    ((kername, global_decl) prod list, __) sigT -> ((kername, global_decl)
    prod list, __) sigT -> ((kername, global_decl) prod list, __) sigT

  val strictly_extends_decls_part_trans :
    global_env -> global_env -> global_env -> ((kername, global_decl) prod
    list, __) sigT -> ((kername, global_decl) prod list, __) sigT ->
    ((kername, global_decl) prod list, __) sigT

  val strictly_extends_decls_trans :
    (global_env, strictly_extends_decls) coq_Transitive

  val extends_decls_trans : (global_env, extends_decls) coq_Transitive

  val extends_strictly_on_decls_trans :
    (global_env, extends_strictly_on_decls) coq_Transitive

  val extends_trans : (global_env, extends) coq_Transitive

  val declared_kername_set : global_declarations -> KernameSet.t

  val merge_globals :
    global_declarations -> global_declarations -> global_declarations

  val merge_global_envs : global_env -> global_env -> global_env

  val strictly_extends_decls_l_merge_globals :
    global_declarations -> global_declarations -> ((kername, global_decl)
    prod list, __) sigT

  val extends_l_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_strictly_on_decls_l_merge :
    global_env -> global_env -> extends_strictly_on_decls

  val extends_l_merge : global_env -> global_env -> extends

  val extends_r_merge_globals :
    global_declarations -> global_declarations -> kername -> (global_decl
    list, __) sigT

  val extends_r_merge : global_env -> global_env -> extends

  val primitive_constant : global_env -> prim_tag -> kername option

  type primitive_invariants = (Universe.t, __) sigT

  type global_env_ext = (global_env, universes_decl) prod

  val fst_ctx : global_env_ext -> global_env

  val empty_ext : global_env -> global_env_ext

  type program = (global_env, term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : term context_decl -> term -> term

  val it_mkLambda_or_LetIn : context -> term -> term

  val mkProd_or_LetIn : term context_decl -> term -> term

  val it_mkProd_or_LetIn : context -> term -> term

  val reln : term list -> nat -> term context_decl list -> term list

  val to_extended_list_k : term context_decl list -> nat -> term list

  val to_extended_list : term context_decl list -> term list

  val reln_alt : nat -> context -> term list

  val arities_context : one_inductive_body list -> term context_decl list

  val map_mutual_inductive_body :
    (nat -> term -> term) -> mutual_inductive_body -> mutual_inductive_body

  val projs : inductive -> nat -> nat -> term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * term * term * 'p
  | Coq_on_vdef of aname * term * term * term * term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> term -> term -> 'a1 -> 'a2) -> (aname -> term -> term -> term
    -> term -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term context_decl
    -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> term -> term -> 'a1 -> 'a2) -> (aname -> term -> term -> term
    -> term -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term context_decl
    -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    term context_decl -> term context_decl -> 'a1 coq_All_decls -> (term
    context_decl * term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    term context_decl -> term context_decl -> ('a1 coq_All_decls, term
    context_decl * term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((term context_decl * term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * term * 
     term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * term * 
     term * term * term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> term -> term -> __ -> 'a1 ->
    'a2) -> (name binder_annot -> name binder_annot -> term -> term -> term
    -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> term -> term -> __ -> 'a1 ->
    'a2) -> (name binder_annot -> name binder_annot -> term -> term -> term
    -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    term context_decl -> term context_decl -> 'a1 coq_All_decls_alpha ->
    (term context_decl * term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    term context_decl -> term context_decl -> ('a1 coq_All_decls_alpha, term
    context_decl * term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((term context_decl * term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    term context_decl -> term context_decl -> 'a1 coq_All_decls -> (term ->
    term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    term context_decl -> term context_decl -> 'a1 coq_All_decls_alpha ->
    (term -> term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    term context_decl -> term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (term context_decl, (term context_decl, term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end

val destArity :
  term context_decl list -> term -> (term context_decl list, Universe.t) prod
  option

val inds : kername -> Instance.t -> Env.one_inductive_body list -> term list

module TemplateTermUtils :
 sig
  val destArity :
    term context_decl list -> term -> (term context_decl list, Universe.t)
    prod option

  val inds : kername -> Instance.t -> Env.one_inductive_body list -> term list
 end

module TemplateLookup :
 sig
  val lookup_constant_gen :
    (kername -> Env.global_decl option) -> kername -> Env.constant_body option

  val lookup_constant : Env.global_env -> kername -> Env.constant_body option

  val lookup_minductive_gen :
    (kername -> Env.global_decl option) -> kername ->
    Env.mutual_inductive_body option

  val lookup_minductive :
    Env.global_env -> kername -> Env.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> Env.global_decl option) -> inductive ->
    (Env.mutual_inductive_body, Env.one_inductive_body) prod option

  val lookup_inductive :
    Env.global_env -> inductive -> (Env.mutual_inductive_body,
    Env.one_inductive_body) prod option

  val lookup_constructor_gen :
    (kername -> Env.global_decl option) -> inductive -> nat ->
    ((Env.mutual_inductive_body, Env.one_inductive_body) prod,
    Env.constructor_body) prod option

  val lookup_constructor :
    Env.global_env -> inductive -> nat -> ((Env.mutual_inductive_body,
    Env.one_inductive_body) prod, Env.constructor_body) prod option

  val lookup_projection_gen :
    (kername -> Env.global_decl option) -> projection ->
    (((Env.mutual_inductive_body, Env.one_inductive_body) prod,
    Env.constructor_body) prod, Env.projection_body) prod option

  val lookup_projection :
    Env.global_env -> projection -> (((Env.mutual_inductive_body,
    Env.one_inductive_body) prod, Env.constructor_body) prod,
    Env.projection_body) prod option

  val on_udecl_decl : (universes_decl -> 'a1) -> Env.global_decl -> 'a1

  val universes_decl_of_decl : Env.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : Env.global_env -> ConstraintSet.t

  val global_uctx : Env.global_env -> ContextSet.t

  val global_ext_levels : Env.global_env_ext -> LevelSet.t

  val global_ext_constraints : Env.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : Env.global_env_ext -> ContextSet.t

  val wf_universe_dec : Env.global_env_ext -> Universe.t -> sumbool

  val declared_ind_declared_constructors :
    checker_flags -> Env.global_env -> inductive -> Env.mutual_inductive_body
    -> Env.one_inductive_body -> (Env.constructor_body, __) coq_Alli
 end

val lookup_constant_gen :
  (kername -> Env.global_decl option) -> kername -> Env.constant_body option

val lookup_constant : Env.global_env -> kername -> Env.constant_body option

val lookup_minductive_gen :
  (kername -> Env.global_decl option) -> kername -> Env.mutual_inductive_body
  option

val lookup_minductive :
  Env.global_env -> kername -> Env.mutual_inductive_body option

val lookup_inductive_gen :
  (kername -> Env.global_decl option) -> inductive ->
  (Env.mutual_inductive_body, Env.one_inductive_body) prod option

val lookup_inductive :
  Env.global_env -> inductive -> (Env.mutual_inductive_body,
  Env.one_inductive_body) prod option

val lookup_constructor_gen :
  (kername -> Env.global_decl option) -> inductive -> nat ->
  ((Env.mutual_inductive_body, Env.one_inductive_body) prod,
  Env.constructor_body) prod option

val lookup_constructor :
  Env.global_env -> inductive -> nat -> ((Env.mutual_inductive_body,
  Env.one_inductive_body) prod, Env.constructor_body) prod option

val lookup_projection_gen :
  (kername -> Env.global_decl option) -> projection ->
  (((Env.mutual_inductive_body, Env.one_inductive_body) prod,
  Env.constructor_body) prod, Env.projection_body) prod option

val lookup_projection :
  Env.global_env -> projection -> (((Env.mutual_inductive_body,
  Env.one_inductive_body) prod, Env.constructor_body) prod,
  Env.projection_body) prod option

val on_udecl_decl : (universes_decl -> 'a1) -> Env.global_decl -> 'a1

val universes_decl_of_decl : Env.global_decl -> universes_decl

val global_levels : ContextSet.t -> LevelSet.t

val global_constraints : Env.global_env -> ConstraintSet.t

val global_uctx : Env.global_env -> ContextSet.t

val global_ext_levels : Env.global_env_ext -> LevelSet.t

val global_ext_constraints : Env.global_env_ext -> ConstraintSet.t

val global_ext_uctx : Env.global_env_ext -> ContextSet.t

val wf_universe_dec : Env.global_env_ext -> Universe.t -> sumbool

val declared_ind_declared_constructors :
  checker_flags -> Env.global_env -> inductive -> Env.mutual_inductive_body
  -> Env.one_inductive_body -> (Env.constructor_body, __) coq_Alli

val tDummy : term

val mkApp : term -> term -> term

val isApp : term -> bool

val isLambda : term -> bool

type parameter_entry = { parameter_entry_type : term;
                         parameter_entry_universes : universes_entry }

val parameter_entry_type : parameter_entry -> term

val parameter_entry_universes : parameter_entry -> universes_entry

type definition_entry = { definition_entry_type : term option;
                          definition_entry_body : term;
                          definition_entry_universes : universes_entry;
                          definition_entry_opaque : bool }

val definition_entry_type : definition_entry -> term option

val definition_entry_body : definition_entry -> term

val definition_entry_universes : definition_entry -> universes_entry

val definition_entry_opaque : definition_entry -> bool

type constant_entry =
| ParameterEntry of parameter_entry
| DefinitionEntry of definition_entry

val constant_entry_rect :
  (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry ->
  'a1

val constant_entry_rec :
  (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry ->
  'a1

type one_inductive_entry = { mind_entry_typename : ident;
                             mind_entry_arity : term;
                             mind_entry_consnames : ident list;
                             mind_entry_lc : term list }

val mind_entry_typename : one_inductive_entry -> ident

val mind_entry_arity : one_inductive_entry -> term

val mind_entry_consnames : one_inductive_entry -> ident list

val mind_entry_lc : one_inductive_entry -> term list

type mutual_inductive_entry = { mind_entry_record : ident option option;
                                mind_entry_finite : recursivity_kind;
                                mind_entry_params : Env.context;
                                mind_entry_inds : one_inductive_entry list;
                                mind_entry_universes : universes_entry;
                                mind_entry_template : bool;
                                mind_entry_variance : Variance.t option list
                                                      option;
                                mind_entry_private : bool option }

val mind_entry_record : mutual_inductive_entry -> ident option option

val mind_entry_finite : mutual_inductive_entry -> recursivity_kind

val mind_entry_params : mutual_inductive_entry -> Env.context

val mind_entry_inds : mutual_inductive_entry -> one_inductive_entry list

val mind_entry_universes : mutual_inductive_entry -> universes_entry

val mind_entry_template : mutual_inductive_entry -> bool

val mind_entry_variance :
  mutual_inductive_entry -> Variance.t option list option

val mind_entry_private : mutual_inductive_entry -> bool option

val ind_predicate_context :
  inductive -> Env.mutual_inductive_body -> Env.one_inductive_body ->
  Env.context

val inst_case_context : term list -> Instance.t -> Env.context -> Env.context

val pre_case_predicate_context_gen :
  inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
  list -> Instance.t -> Env.context

val case_predicate_context_gen :
  inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
  list -> Instance.t -> aname list -> term context_decl list

val case_predicate_context :
  inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
  predicate -> Env.context

val cstr_branch_context :
  inductive -> Env.mutual_inductive_body -> Env.constructor_body ->
  Env.context

val case_branch_context_gen :
  inductive -> Env.mutual_inductive_body -> term list -> Instance.t -> aname
  list -> Env.constructor_body -> Env.context

val case_branch_context :
  inductive -> Env.mutual_inductive_body -> Env.constructor_body -> term
  predicate -> term branch -> Env.context

val case_branches_contexts_gen :
  inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
  list -> Instance.t -> term branch list -> Env.context list

val case_branches_contexts :
  inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
  predicate -> term branch list -> Env.context list

val case_branch_type_gen :
  inductive -> Env.mutual_inductive_body -> term list -> Instance.t -> term
  -> nat -> Env.constructor_body -> term branch -> (Env.context, term) prod

val case_branch_type :
  inductive -> Env.mutual_inductive_body -> term predicate -> term -> nat ->
  Env.constructor_body -> term branch -> (Env.context, term) prod
