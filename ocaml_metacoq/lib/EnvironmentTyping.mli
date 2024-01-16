open All_Forall
open BasicAst
open BinNums
open CRelationClasses
open Classes
open Datatypes
open Kernames
open List
open MCList
open MCProd
open Nat
open Primitive
open Signature
open Specif
open Universes
open Config

type __ = Obj.t

module Lookup :
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 sig
  val lookup_constant_gen :
    (kername -> E.global_decl option) -> kername -> E.constant_body option

  val lookup_constant : E.global_env -> kername -> E.constant_body option

  val lookup_minductive_gen :
    (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
    option

  val lookup_minductive :
    E.global_env -> kername -> E.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> E.global_decl option) -> inductive ->
    (E.mutual_inductive_body, E.one_inductive_body) prod option

  val lookup_inductive :
    E.global_env -> inductive -> (E.mutual_inductive_body,
    E.one_inductive_body) prod option

  val lookup_constructor_gen :
    (kername -> E.global_decl option) -> inductive -> nat ->
    ((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod option

  val lookup_constructor :
    E.global_env -> inductive -> nat -> ((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod option

  val lookup_projection_gen :
    (kername -> E.global_decl option) -> projection ->
    (((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod, E.projection_body) prod option

  val lookup_projection :
    E.global_env -> projection -> (((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod, E.projection_body)
    prod option

  val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1

  val universes_decl_of_decl : E.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : E.global_env -> ConstraintSet.t

  val global_uctx : E.global_env -> ContextSet.t

  val global_ext_levels : E.global_env_ext -> LevelSet.t

  val global_ext_constraints : E.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : E.global_env_ext -> ContextSet.t

  val wf_universe_dec : E.global_env_ext -> Universe.t -> sumbool

  val declared_ind_declared_constructors :
    checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body ->
    E.one_inductive_body -> (E.constructor_body, __) coq_Alli
 end

module type LookupSig =
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 sig
  val lookup_constant_gen :
    (kername -> E.global_decl option) -> kername -> E.constant_body option

  val lookup_constant : E.global_env -> kername -> E.constant_body option

  val lookup_minductive_gen :
    (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
    option

  val lookup_minductive :
    E.global_env -> kername -> E.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> E.global_decl option) -> inductive ->
    (E.mutual_inductive_body, E.one_inductive_body) prod option

  val lookup_inductive :
    E.global_env -> inductive -> (E.mutual_inductive_body,
    E.one_inductive_body) prod option

  val lookup_constructor_gen :
    (kername -> E.global_decl option) -> inductive -> nat ->
    ((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod option

  val lookup_constructor :
    E.global_env -> inductive -> nat -> ((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod option

  val lookup_projection_gen :
    (kername -> E.global_decl option) -> projection ->
    (((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod, E.projection_body) prod option

  val lookup_projection :
    E.global_env -> projection -> (((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod, E.projection_body)
    prod option

  val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1

  val universes_decl_of_decl : E.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : E.global_env -> ConstraintSet.t

  val global_uctx : E.global_env -> ContextSet.t

  val global_ext_levels : E.global_env_ext -> LevelSet.t

  val global_ext_constraints : E.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : E.global_env_ext -> ContextSet.t

  val wf_universe_dec : E.global_env_ext -> Universe.t -> sumbool

  val declared_ind_declared_constructors :
    checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body ->
    E.one_inductive_body -> (E.constructor_body, __) coq_Alli
 end

module EnvTyping :
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end

module type EnvTypingSig =
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end

module Conversion :
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end

module type ConversionSig =
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end

module GlobalMaps :
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 functor (C:sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end) ->
 functor (L:sig
  val lookup_constant_gen :
    (kername -> E.global_decl option) -> kername -> E.constant_body option

  val lookup_constant : E.global_env -> kername -> E.constant_body option

  val lookup_minductive_gen :
    (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
    option

  val lookup_minductive :
    E.global_env -> kername -> E.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> E.global_decl option) -> inductive ->
    (E.mutual_inductive_body, E.one_inductive_body) prod option

  val lookup_inductive :
    E.global_env -> inductive -> (E.mutual_inductive_body,
    E.one_inductive_body) prod option

  val lookup_constructor_gen :
    (kername -> E.global_decl option) -> inductive -> nat ->
    ((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod option

  val lookup_constructor :
    E.global_env -> inductive -> nat -> ((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod option

  val lookup_projection_gen :
    (kername -> E.global_decl option) -> projection ->
    (((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod, E.projection_body) prod option

  val lookup_projection :
    E.global_env -> projection -> (((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod, E.projection_body)
    prod option

  val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1

  val universes_decl_of_decl : E.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : E.global_env -> ConstraintSet.t

  val global_uctx : E.global_env -> ContextSet.t

  val global_ext_levels : E.global_env_ext -> LevelSet.t

  val global_ext_constraints : E.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : E.global_env_ext -> ContextSet.t

  val wf_universe_dec : E.global_env_ext -> Universe.t -> sumbool

  val declared_ind_declared_constructors :
    checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body ->
    E.one_inductive_body -> (E.constructor_body, __) coq_Alli
 end) ->
 sig
  type 'p on_context = 'p ET.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t

  val ind_realargs : E.one_inductive_body -> nat

  type positive_cstr_arg =
  | Coq_pos_arg_closed of T.term
  | Coq_pos_arg_concl of T.term list * nat * E.one_inductive_body
     * (T.term, __) coq_All
  | Coq_pos_arg_let of aname * T.term * T.term * T.term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * T.term * T.term * positive_cstr_arg

  val positive_cstr_arg_rect :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  val positive_cstr_arg_rec :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  type positive_cstr =
  | Coq_pos_concl of T.term list * (T.term, __) coq_All
  | Coq_pos_let of aname * T.term * T.term * T.term * positive_cstr
  | Coq_pos_ass of aname * T.term * T.term * positive_cstr_arg * positive_cstr

  val positive_cstr_rect :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val positive_cstr_rec :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val lift_level : nat -> Level.t_ -> Level.t_

  val lift_instance : nat -> Level.t_ list -> Level.t_ list

  val lift_constraint :
    nat -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t_,
    ConstraintType.t) prod, Level.t_) prod

  val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

  val level_var_instance : nat -> name list -> Level.t_ list

  val variance_cstrs :
    Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

  val variance_universes :
    universes_decl -> Variance.t list -> ((universes_decl, Level.t_ list)
    prod, Level.t_ list) prod option

  val ind_arities : E.mutual_inductive_body -> T.term context_decl list

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  val cstr_concl_head :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  val cstr_concl :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p ET.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  val on_ctype :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 on_type

  val on_cargs :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx

  val on_cindices :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 ET.ctx_inst

  val on_ctype_positive :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> positive_cstr

  val on_ctype_variance :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
    cstr_respects_variance

  type ('pcmp, 'p) on_constructors =
    (E.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor) coq_All2

  type on_projections =
    (E.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  val on_projs :
    E.mutual_inductive_body -> kername -> nat -> E.one_inductive_body ->
    E.context -> E.constructor_body -> on_projections -> (E.projection_body,
    __) coq_Alli

  type constructor_univs = Universe.t list

  val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

  val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = { onArity : 'p on_type;
                                   ind_cunivs : constructor_univs list;
                                   onConstructors : ('pcmp, 'p)
                                                    on_constructors;
                                   onProjections : __;
                                   ind_sorts : 'p check_ind_sorts;
                                   onIndices : __ }

  val onArity :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type

  val ind_cunivs :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    constructor_univs list

  val onConstructors :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
    on_constructors

  val onProjections :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  val ind_sorts :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    check_ind_sorts

  val onIndices :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (E.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  val onInductives :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> (E.one_inductive_body, ('a1, 'a2)
    on_ind_body) coq_Alli

  val onParams :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> 'a2 on_context

  val onVariance :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> on_variance

  type 'p on_constant_decl = __

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> universes_decl

  val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> ('a1, 'a2) on_global_decl

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of E.global_declarations * kername * E.global_decl
     * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

  val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> ('a1, 'a2) on_global_decls ->
    E.global_declarations * ('a1, 'a2) on_global_decls

  val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> (('a1, 'a2) on_global_decls,
    E.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature

  type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

  type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

  val type_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> __ list ->
    (__, __ type_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort ->
    (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
    type_local_ctx

  val type_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> 'a1
    type_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2) ->
    'a2 type_local_ctx

  val sorts_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> __ list
    -> (__, __ sorts_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort
    -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx) coq_All -> 'a1
    sorts_local_ctx

  val sorts_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> 'a1
    sorts_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2)
    -> 'a2 sorts_local_ctx

  val cstr_respects_variance_impl_gen :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT ->
    __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
    cstr_respects_variance

  val cstr_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
    cstr_respects_variance

  val on_constructor_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ((checker_flags, __) prod, __) prod list -> checker_flags ->
    (((checker_flags, __) prod, __) prod, __) sigT -> (E.context -> T.term ->
    E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructor

  val on_constructors_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body list ->
    Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> (E.context -> T.term
    -> E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructors

  val ind_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list -> E.context
    -> __ -> 'a1 ind_respects_variance -> 'a2 ind_respects_variance

  val on_variance_impl :
    E.global_env -> universes_decl -> Variance.t list option -> checker_flags
    -> checker_flags -> on_variance -> on_variance

  val on_global_env_impl_config :
    checker_flags -> checker_flags -> ((E.global_env, universes_decl) prod ->
    E.context -> T.term -> E.typ_or_sort -> ('a1, 'a3) on_global_env -> ('a2,
    'a4) on_global_env -> 'a3 -> 'a4) -> ((E.global_env, universes_decl) prod
    -> E.context -> T.term -> T.term -> conv_pb -> ('a1, 'a3) on_global_env
    -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) -> E.global_env -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env

  val on_global_env_impl :
    checker_flags -> ((E.global_env, universes_decl) prod -> E.context ->
    T.term -> E.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env -> 'a2 -> 'a3) -> E.global_env -> ('a1, 'a2) on_global_env
    -> ('a1, 'a3) on_global_env
 end

module type GlobalMapsSig =
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 functor (C:sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end) ->
 functor (L:sig
  val lookup_constant_gen :
    (kername -> E.global_decl option) -> kername -> E.constant_body option

  val lookup_constant : E.global_env -> kername -> E.constant_body option

  val lookup_minductive_gen :
    (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
    option

  val lookup_minductive :
    E.global_env -> kername -> E.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> E.global_decl option) -> inductive ->
    (E.mutual_inductive_body, E.one_inductive_body) prod option

  val lookup_inductive :
    E.global_env -> inductive -> (E.mutual_inductive_body,
    E.one_inductive_body) prod option

  val lookup_constructor_gen :
    (kername -> E.global_decl option) -> inductive -> nat ->
    ((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod option

  val lookup_constructor :
    E.global_env -> inductive -> nat -> ((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod option

  val lookup_projection_gen :
    (kername -> E.global_decl option) -> projection ->
    (((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod, E.projection_body) prod option

  val lookup_projection :
    E.global_env -> projection -> (((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod, E.projection_body)
    prod option

  val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1

  val universes_decl_of_decl : E.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : E.global_env -> ConstraintSet.t

  val global_uctx : E.global_env -> ContextSet.t

  val global_ext_levels : E.global_env_ext -> LevelSet.t

  val global_ext_constraints : E.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : E.global_env_ext -> ContextSet.t

  val wf_universe_dec : E.global_env_ext -> Universe.t -> sumbool

  val declared_ind_declared_constructors :
    checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body ->
    E.one_inductive_body -> (E.constructor_body, __) coq_Alli
 end) ->
 sig
  type 'p on_context = 'p ET.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t

  val ind_realargs : E.one_inductive_body -> nat

  type positive_cstr_arg =
  | Coq_pos_arg_closed of T.term
  | Coq_pos_arg_concl of T.term list * nat * E.one_inductive_body
     * (T.term, __) coq_All
  | Coq_pos_arg_let of aname * T.term * T.term * T.term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * T.term * T.term * positive_cstr_arg

  val positive_cstr_arg_rect :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  val positive_cstr_arg_rec :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  type positive_cstr =
  | Coq_pos_concl of T.term list * (T.term, __) coq_All
  | Coq_pos_let of aname * T.term * T.term * T.term * positive_cstr
  | Coq_pos_ass of aname * T.term * T.term * positive_cstr_arg * positive_cstr

  val positive_cstr_rect :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val positive_cstr_rec :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val lift_level : nat -> Level.t_ -> Level.t_

  val lift_instance : nat -> Level.t_ list -> Level.t_ list

  val lift_constraint :
    nat -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t_,
    ConstraintType.t) prod, Level.t_) prod

  val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

  val level_var_instance : nat -> name list -> Level.t_ list

  val variance_cstrs :
    Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

  val variance_universes :
    universes_decl -> Variance.t list -> ((universes_decl, Level.t_ list)
    prod, Level.t_ list) prod option

  val ind_arities : E.mutual_inductive_body -> T.term context_decl list

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  val cstr_concl_head :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  val cstr_concl :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p ET.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  val on_ctype :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 on_type

  val on_cargs :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx

  val on_cindices :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 ET.ctx_inst

  val on_ctype_positive :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> positive_cstr

  val on_ctype_variance :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
    cstr_respects_variance

  type ('pcmp, 'p) on_constructors =
    (E.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor) coq_All2

  type on_projections =
    (E.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  val on_projs :
    E.mutual_inductive_body -> kername -> nat -> E.one_inductive_body ->
    E.context -> E.constructor_body -> on_projections -> (E.projection_body,
    __) coq_Alli

  type constructor_univs = Universe.t list

  val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

  val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = { onArity : 'p on_type;
                                   ind_cunivs : constructor_univs list;
                                   onConstructors : ('pcmp, 'p)
                                                    on_constructors;
                                   onProjections : __;
                                   ind_sorts : 'p check_ind_sorts;
                                   onIndices : __ }

  val onArity :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type

  val ind_cunivs :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    constructor_univs list

  val onConstructors :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
    on_constructors

  val onProjections :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  val ind_sorts :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    check_ind_sorts

  val onIndices :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (E.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  val onInductives :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> (E.one_inductive_body, ('a1, 'a2)
    on_ind_body) coq_Alli

  val onParams :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> 'a2 on_context

  val onVariance :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> on_variance

  type 'p on_constant_decl = __

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> universes_decl

  val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> ('a1, 'a2) on_global_decl

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of E.global_declarations * kername * E.global_decl
     * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

  val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> ('a1, 'a2) on_global_decls ->
    E.global_declarations * ('a1, 'a2) on_global_decls

  val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> (('a1, 'a2) on_global_decls,
    E.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature

  type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

  type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

  val type_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> __ list ->
    (__, __ type_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort ->
    (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
    type_local_ctx

  val type_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> 'a1
    type_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2) ->
    'a2 type_local_ctx

  val sorts_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> __ list
    -> (__, __ sorts_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort
    -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx) coq_All -> 'a1
    sorts_local_ctx

  val sorts_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> 'a1
    sorts_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2)
    -> 'a2 sorts_local_ctx

  val cstr_respects_variance_impl_gen :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT ->
    __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
    cstr_respects_variance

  val cstr_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
    cstr_respects_variance

  val on_constructor_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ((checker_flags, __) prod, __) prod list -> checker_flags ->
    (((checker_flags, __) prod, __) prod, __) sigT -> (E.context -> T.term ->
    E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructor

  val on_constructors_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body list ->
    Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> (E.context -> T.term
    -> E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructors

  val ind_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list -> E.context
    -> __ -> 'a1 ind_respects_variance -> 'a2 ind_respects_variance

  val on_variance_impl :
    E.global_env -> universes_decl -> Variance.t list option -> checker_flags
    -> checker_flags -> on_variance -> on_variance

  val on_global_env_impl_config :
    checker_flags -> checker_flags -> ((E.global_env, universes_decl) prod ->
    E.context -> T.term -> E.typ_or_sort -> ('a1, 'a3) on_global_env -> ('a2,
    'a4) on_global_env -> 'a3 -> 'a4) -> ((E.global_env, universes_decl) prod
    -> E.context -> T.term -> T.term -> conv_pb -> ('a1, 'a3) on_global_env
    -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) -> E.global_env -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env

  val on_global_env_impl :
    checker_flags -> ((E.global_env, universes_decl) prod -> E.context ->
    T.term -> E.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env -> 'a2 -> 'a3) -> E.global_env -> ('a1, 'a2) on_global_env
    -> ('a1, 'a3) on_global_env
 end

module type ConversionParSig =
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 sig
  type cumul_gen
 end

module type Typing =
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 functor (CT:sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end) ->
 functor (CS:sig
  type cumul_gen
 end) ->
 sig
  type typing
 end

module DeclarationTyping :
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 functor (CT:sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end) ->
 functor (CS:sig
  type cumul_gen
 end) ->
 functor (Ty:sig
  type typing
 end) ->
 functor (L:sig
  val lookup_constant_gen :
    (kername -> E.global_decl option) -> kername -> E.constant_body option

  val lookup_constant : E.global_env -> kername -> E.constant_body option

  val lookup_minductive_gen :
    (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
    option

  val lookup_minductive :
    E.global_env -> kername -> E.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> E.global_decl option) -> inductive ->
    (E.mutual_inductive_body, E.one_inductive_body) prod option

  val lookup_inductive :
    E.global_env -> inductive -> (E.mutual_inductive_body,
    E.one_inductive_body) prod option

  val lookup_constructor_gen :
    (kername -> E.global_decl option) -> inductive -> nat ->
    ((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod option

  val lookup_constructor :
    E.global_env -> inductive -> nat -> ((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod option

  val lookup_projection_gen :
    (kername -> E.global_decl option) -> projection ->
    (((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod, E.projection_body) prod option

  val lookup_projection :
    E.global_env -> projection -> (((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod, E.projection_body)
    prod option

  val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1

  val universes_decl_of_decl : E.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : E.global_env -> ConstraintSet.t

  val global_uctx : E.global_env -> ContextSet.t

  val global_ext_levels : E.global_env_ext -> LevelSet.t

  val global_ext_constraints : E.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : E.global_env_ext -> ContextSet.t

  val wf_universe_dec : E.global_env_ext -> Universe.t -> sumbool

  val declared_ind_declared_constructors :
    checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body ->
    E.one_inductive_body -> (E.constructor_body, __) coq_Alli
 end) ->
 functor (GM:sig
  type 'p on_context = 'p ET.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t

  val ind_realargs : E.one_inductive_body -> nat

  type positive_cstr_arg =
  | Coq_pos_arg_closed of T.term
  | Coq_pos_arg_concl of T.term list * nat * E.one_inductive_body
     * (T.term, __) coq_All
  | Coq_pos_arg_let of aname * T.term * T.term * T.term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * T.term * T.term * positive_cstr_arg

  val positive_cstr_arg_rect :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  val positive_cstr_arg_rec :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  type positive_cstr =
  | Coq_pos_concl of T.term list * (T.term, __) coq_All
  | Coq_pos_let of aname * T.term * T.term * T.term * positive_cstr
  | Coq_pos_ass of aname * T.term * T.term * positive_cstr_arg * positive_cstr

  val positive_cstr_rect :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val positive_cstr_rec :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val lift_level : nat -> Level.t_ -> Level.t_

  val lift_instance : nat -> Level.t_ list -> Level.t_ list

  val lift_constraint :
    nat -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t_,
    ConstraintType.t) prod, Level.t_) prod

  val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

  val level_var_instance : nat -> name list -> Level.t_ list

  val variance_cstrs :
    Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

  val variance_universes :
    universes_decl -> Variance.t list -> ((universes_decl, Level.t_ list)
    prod, Level.t_ list) prod option

  val ind_arities : E.mutual_inductive_body -> T.term context_decl list

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  val cstr_concl_head :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  val cstr_concl :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p ET.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  val on_ctype :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 on_type

  val on_cargs :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx

  val on_cindices :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 ET.ctx_inst

  val on_ctype_positive :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> positive_cstr

  val on_ctype_variance :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
    cstr_respects_variance

  type ('pcmp, 'p) on_constructors =
    (E.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor) coq_All2

  type on_projections =
    (E.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  val on_projs :
    E.mutual_inductive_body -> kername -> nat -> E.one_inductive_body ->
    E.context -> E.constructor_body -> on_projections -> (E.projection_body,
    __) coq_Alli

  type constructor_univs = Universe.t list

  val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

  val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = { onArity : 'p on_type;
                                   ind_cunivs : constructor_univs list;
                                   onConstructors : ('pcmp, 'p)
                                                    on_constructors;
                                   onProjections : __;
                                   ind_sorts : 'p check_ind_sorts;
                                   onIndices : __ }

  val onArity :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type

  val ind_cunivs :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    constructor_univs list

  val onConstructors :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
    on_constructors

  val onProjections :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  val ind_sorts :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    check_ind_sorts

  val onIndices :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (E.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  val onInductives :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> (E.one_inductive_body, ('a1, 'a2)
    on_ind_body) coq_Alli

  val onParams :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> 'a2 on_context

  val onVariance :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> on_variance

  type 'p on_constant_decl = __

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> universes_decl

  val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> ('a1, 'a2) on_global_decl

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of E.global_declarations * kername * E.global_decl
     * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

  val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> ('a1, 'a2) on_global_decls ->
    E.global_declarations * ('a1, 'a2) on_global_decls

  val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> (('a1, 'a2) on_global_decls,
    E.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature

  type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

  type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

  val type_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> __ list ->
    (__, __ type_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort ->
    (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
    type_local_ctx

  val type_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> 'a1
    type_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2) ->
    'a2 type_local_ctx

  val sorts_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> __ list
    -> (__, __ sorts_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort
    -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx) coq_All -> 'a1
    sorts_local_ctx

  val sorts_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> 'a1
    sorts_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2)
    -> 'a2 sorts_local_ctx

  val cstr_respects_variance_impl_gen :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT ->
    __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
    cstr_respects_variance

  val cstr_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
    cstr_respects_variance

  val on_constructor_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ((checker_flags, __) prod, __) prod list -> checker_flags ->
    (((checker_flags, __) prod, __) prod, __) sigT -> (E.context -> T.term ->
    E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructor

  val on_constructors_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body list ->
    Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> (E.context -> T.term
    -> E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructors

  val ind_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list -> E.context
    -> __ -> 'a1 ind_respects_variance -> 'a2 ind_respects_variance

  val on_variance_impl :
    E.global_env -> universes_decl -> Variance.t list option -> checker_flags
    -> checker_flags -> on_variance -> on_variance

  val on_global_env_impl_config :
    checker_flags -> checker_flags -> ((E.global_env, universes_decl) prod ->
    E.context -> T.term -> E.typ_or_sort -> ('a1, 'a3) on_global_env -> ('a2,
    'a4) on_global_env -> 'a3 -> 'a4) -> ((E.global_env, universes_decl) prod
    -> E.context -> T.term -> T.term -> conv_pb -> ('a1, 'a3) on_global_env
    -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) -> E.global_env -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env

  val on_global_env_impl :
    checker_flags -> ((E.global_env, universes_decl) prod -> E.context ->
    T.term -> E.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env -> 'a2 -> 'a3) -> E.global_env -> ('a1, 'a2) on_global_env
    -> ('a1, 'a3) on_global_env
 end) ->
 sig
  type isType = Ty.typing ET.infer_sort

  type 'p coq_Forall_decls_typing =
    (CS.cumul_gen, 'p ET.lift_typing) GM.on_global_env

  type type_local_decl = __

  val refine_type :
    checker_flags -> E.global_env_ext -> E.context -> T.term -> T.term ->
    T.term -> Ty.typing -> Ty.typing

  type wf_local_rel = Ty.typing ET.lift_typing ET.coq_All_local_rel

  val on_wf_global_env_impl_config :
    checker_flags -> checker_flags -> checker_flags -> E.global_env ->
    (CS.cumul_gen, Ty.typing ET.lift_typing) GM.on_global_env ->
    (E.global_env_ext -> E.context -> conv_pb -> T.term -> T.term ->
    CS.cumul_gen -> CS.cumul_gen) -> ((E.global_env, universes_decl) prod ->
    E.context -> T.term -> E.typ_or_sort -> (CS.cumul_gen, Ty.typing
    ET.lift_typing) GM.on_global_env -> (CS.cumul_gen, 'a1) GM.on_global_env
    -> (CS.cumul_gen, 'a2) GM.on_global_env -> 'a1 -> 'a2) -> (CS.cumul_gen,
    'a1) GM.on_global_env -> (CS.cumul_gen, 'a2) GM.on_global_env

  val on_wf_global_env_impl :
    checker_flags -> E.global_env -> (CS.cumul_gen, Ty.typing ET.lift_typing)
    GM.on_global_env -> ((E.global_env, universes_decl) prod -> E.context ->
    T.term -> E.typ_or_sort -> (CS.cumul_gen, Ty.typing ET.lift_typing)
    GM.on_global_env -> (CS.cumul_gen, 'a1) GM.on_global_env ->
    (CS.cumul_gen, 'a2) GM.on_global_env -> 'a1 -> 'a2) -> (CS.cumul_gen,
    'a1) GM.on_global_env -> (CS.cumul_gen, 'a2) GM.on_global_env
 end

module type DeclarationTypingSig =
 functor (T:Environment.Term) ->
 functor (E:sig
  type typ_or_sort = T.term typ_or_sort_

  val vass : aname -> T.term -> T.term context_decl

  val vdef : aname -> T.term -> T.term -> T.term context_decl

  type context = T.term context_decl list

  val lift_decl : nat -> nat -> T.term context_decl -> T.term context_decl

  val lift_context : nat -> nat -> context -> context

  val subst_context : T.term list -> nat -> context -> context

  val subst_decl :
    T.term list -> nat -> T.term context_decl -> T.term context_decl

  val subst_telescope : T.term list -> nat -> context -> context

  val subst_instance_decl : T.term context_decl coq_UnivSubst

  val subst_instance_context : context coq_UnivSubst

  val set_binder_name : aname -> T.term context_decl -> T.term context_decl

  val context_assumptions : context -> nat

  val is_assumption_context : context -> bool

  val smash_context : context -> context -> context

  val extended_subst : context -> nat -> T.term list

  val expand_lets_k : context -> nat -> T.term -> T.term

  val expand_lets : context -> T.term -> T.term

  val expand_lets_k_ctx : context -> nat -> context -> context

  val expand_lets_ctx : context -> context -> context

  val fix_context : T.term mfixpoint -> context

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  val cstr_name : constructor_body -> ident

  val cstr_args : constructor_body -> context

  val cstr_indices : constructor_body -> T.term list

  val cstr_type : constructor_body -> T.term

  val cstr_arity : constructor_body -> nat

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  val proj_name : projection_body -> ident

  val proj_relevance : projection_body -> relevance

  val proj_type : projection_body -> T.term

  val map_constructor_body :
    nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
    constructor_body

  val map_projection_body :
    nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  val ind_name : one_inductive_body -> ident

  val ind_indices : one_inductive_body -> context

  val ind_sort : one_inductive_body -> Universe.t

  val ind_type : one_inductive_body -> T.term

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_ctors : one_inductive_body -> constructor_body list

  val ind_projs : one_inductive_body -> projection_body list

  val ind_relevance : one_inductive_body -> relevance

  val map_one_inductive_body :
    nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
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

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  val cst_type : constant_body -> T.term

  val cst_body : constant_body -> T.term option

  val cst_universes : constant_body -> universes_decl

  val cst_relevance : constant_body -> relevance

  val map_constant_body : (T.term -> T.term) -> constant_body -> constant_body

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

  type program = (global_env, T.term) prod

  val app_context : context -> context -> context

  val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkLambda_or_LetIn : context -> T.term -> T.term

  val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term

  val it_mkProd_or_LetIn : context -> T.term -> T.term

  val reln : T.term list -> nat -> T.term context_decl list -> T.term list

  val to_extended_list_k : T.term context_decl list -> nat -> T.term list

  val to_extended_list : T.term context_decl list -> T.term list

  val reln_alt : nat -> context -> T.term list

  val arities_context : one_inductive_body list -> T.term context_decl list

  val map_mutual_inductive_body :
    (nat -> T.term -> T.term) -> mutual_inductive_body ->
    mutual_inductive_body

  val projs : inductive -> nat -> nat -> T.term list

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_rect :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  val coq_All_decls_rec :
    (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
    -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls -> 'a2

  type 'p coq_All_decls_sig = 'p coq_All_decls

  val coq_All_decls_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls

  val coq_All_decls_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls, T.term
    context_decl * T.term context_decl, 'a1 coq_All_decls_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
    coq_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_rect :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  val coq_All_decls_alpha_rec :
    (name binder_annot -> name binder_annot -> T.term -> T.term -> __ -> 'a1
    -> 'a2) -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
    T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  val coq_All_decls_alpha_sig_pack :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha

  val coq_All_decls_alpha_Signature :
    T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
    T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
    coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha :
    ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
    coq_NoConfusionPackage

  val coq_All_decls_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

  val coq_All_decls_alpha_impl :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha ->
    (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha

  val coq_All_decls_to_alpha :
    T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
    coq_All_decls_alpha

  type 'p coq_All2_fold_over =
    (T.term context_decl, (T.term context_decl, T.term context_decl, 'p)
    coq_All_over) coq_All2_fold
 end) ->
 functor (TU:sig
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end) ->
 functor (ET:sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env

  val coq_All_local_env_Signature :
    E.context -> ('a1 coq_All_local_env, E.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
    E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel -> 'a1
    -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    E.context -> E.context -> T.term -> T.term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    E.context -> E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel
    -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment -> (T.term -> 'a1
    -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val infer_typing_sort_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2)
    -> 'a2 infer_sort

  val lift_typing_impl :
    E.global_env_ext -> E.global_env_ext -> E.context -> E.context -> T.term
    -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1 -> 'a2)
    -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of E.context * aname * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of E.context * aname * T.term * T.term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env ->
    ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * T.term * T.term * T.term list * E.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * T.term * T.term * T.term list * E.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
    T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term list * E.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
    ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
    (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
    -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1 ctx_inst
    -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 -> size)
    -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env -> size

  val lift_judgment_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
    lift_judgment -> size

  val lift_typing_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2
    infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
    (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size) ->
    E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_rel -> size
 end) ->
 functor (CT:sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term ->
    __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
    T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
    context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (T.term context_decl * T.term
    context_decl) * 'a1 coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
    coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
    T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end) ->
 functor (CS:sig
  type cumul_gen
 end) ->
 functor (Ty:sig
  type typing
 end) ->
 functor (L:sig
  val lookup_constant_gen :
    (kername -> E.global_decl option) -> kername -> E.constant_body option

  val lookup_constant : E.global_env -> kername -> E.constant_body option

  val lookup_minductive_gen :
    (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
    option

  val lookup_minductive :
    E.global_env -> kername -> E.mutual_inductive_body option

  val lookup_inductive_gen :
    (kername -> E.global_decl option) -> inductive ->
    (E.mutual_inductive_body, E.one_inductive_body) prod option

  val lookup_inductive :
    E.global_env -> inductive -> (E.mutual_inductive_body,
    E.one_inductive_body) prod option

  val lookup_constructor_gen :
    (kername -> E.global_decl option) -> inductive -> nat ->
    ((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod option

  val lookup_constructor :
    E.global_env -> inductive -> nat -> ((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod option

  val lookup_projection_gen :
    (kername -> E.global_decl option) -> projection ->
    (((E.mutual_inductive_body, E.one_inductive_body) prod,
    E.constructor_body) prod, E.projection_body) prod option

  val lookup_projection :
    E.global_env -> projection -> (((E.mutual_inductive_body,
    E.one_inductive_body) prod, E.constructor_body) prod, E.projection_body)
    prod option

  val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1

  val universes_decl_of_decl : E.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : E.global_env -> ConstraintSet.t

  val global_uctx : E.global_env -> ContextSet.t

  val global_ext_levels : E.global_env_ext -> LevelSet.t

  val global_ext_constraints : E.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : E.global_env_ext -> ContextSet.t

  val wf_universe_dec : E.global_env_ext -> Universe.t -> sumbool

  val declared_ind_declared_constructors :
    checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body ->
    E.one_inductive_body -> (E.constructor_body, __) coq_Alli
 end) ->
 functor (GM:sig
  type 'p on_context = 'p ET.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t

  val ind_realargs : E.one_inductive_body -> nat

  type positive_cstr_arg =
  | Coq_pos_arg_closed of T.term
  | Coq_pos_arg_concl of T.term list * nat * E.one_inductive_body
     * (T.term, __) coq_All
  | Coq_pos_arg_let of aname * T.term * T.term * T.term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * T.term * T.term * positive_cstr_arg

  val positive_cstr_arg_rect :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  val positive_cstr_arg_rec :
    E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
    'a1) -> (T.term context_decl list -> T.term list -> nat ->
    E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
    positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname ->
    T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
    context_decl list -> T.term -> positive_cstr_arg -> 'a1

  type positive_cstr =
  | Coq_pos_concl of T.term list * (T.term, __) coq_All
  | Coq_pos_let of aname * T.term * T.term * T.term * positive_cstr
  | Coq_pos_ass of aname * T.term * T.term * positive_cstr_arg * positive_cstr

  val positive_cstr_rect :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val positive_cstr_rec :
    E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
    list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
    aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
    (T.term context_decl list -> aname -> T.term -> T.term ->
    positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term context_decl
    list -> T.term -> positive_cstr -> 'a1

  val lift_level : nat -> Level.t_ -> Level.t_

  val lift_instance : nat -> Level.t_ list -> Level.t_ list

  val lift_constraint :
    nat -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t_,
    ConstraintType.t) prod, Level.t_) prod

  val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

  val level_var_instance : nat -> name list -> Level.t_ list

  val variance_cstrs :
    Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

  val variance_universes :
    universes_decl -> Variance.t list -> ((universes_decl, Level.t_ list)
    prod, Level.t_ list) prod option

  val ind_arities : E.mutual_inductive_body -> T.term context_decl list

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  val cstr_concl_head :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  val cstr_concl :
    E.mutual_inductive_body -> nat -> E.constructor_body -> T.term

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p ET.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  val on_ctype :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 on_type

  val on_cargs :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx

  val on_cindices :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> 'a2 ET.ctx_inst

  val on_ctype_positive :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> positive_cstr

  val on_ctype_variance :
    checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
    cstr_respects_variance

  type ('pcmp, 'p) on_constructors =
    (E.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor) coq_All2

  type on_projections =
    (E.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  val on_projs :
    E.mutual_inductive_body -> kername -> nat -> E.one_inductive_body ->
    E.context -> E.constructor_body -> on_projections -> (E.projection_body,
    __) coq_Alli

  type constructor_univs = Universe.t list

  val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

  val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = { onArity : 'p on_type;
                                   ind_cunivs : constructor_univs list;
                                   onConstructors : ('pcmp, 'p)
                                                    on_constructors;
                                   onProjections : __;
                                   ind_sorts : 'p check_ind_sorts;
                                   onIndices : __ }

  val onArity :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type

  val ind_cunivs :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    constructor_univs list

  val onConstructors :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
    on_constructors

  val onProjections :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  val ind_sorts :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    check_ind_sorts

  val onIndices :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (E.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  val onInductives :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> (E.one_inductive_body, ('a1, 'a2)
    on_ind_body) coq_Alli

  val onParams :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> 'a2 on_context

  val onVariance :
    checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
    -> ('a1, 'a2) on_inductive -> on_variance

  type 'p on_constant_decl = __

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> universes_decl

  val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls_data -> ('a1, 'a2) on_global_decl

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of E.global_declarations * kername * E.global_decl
     * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

  val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> ('a1, 'a2) on_global_decls ->
    E.global_declarations * ('a1, 'a2) on_global_decls

  val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    E.global_declarations -> (('a1, 'a2) on_global_decls,
    E.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature

  type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

  type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

  val type_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> __ list ->
    (__, __ type_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort ->
    (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
    type_local_ctx

  val type_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t -> 'a1
    type_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2) ->
    'a2 type_local_ctx

  val sorts_local_ctx_impl_gen :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> __ list
    -> (__, __ sorts_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort
    -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx) coq_All -> 'a1
    sorts_local_ctx

  val sorts_local_ctx_impl :
    E.global_env_ext -> E.context -> E.context -> Universe.t list -> 'a1
    sorts_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2)
    -> 'a2 sorts_local_ctx

  val cstr_respects_variance_impl_gen :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT ->
    __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
    cstr_respects_variance

  val cstr_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list ->
    E.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
    cstr_respects_variance

  val on_constructor_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
    list -> ((checker_flags, __) prod, __) prod list -> checker_flags ->
    (((checker_flags, __) prod, __) prod, __) sigT -> (E.context -> T.term ->
    E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructor

  val on_constructors_impl_config_gen :
    E.global_env_ext -> E.mutual_inductive_body -> nat ->
    E.one_inductive_body -> E.context -> E.constructor_body list ->
    Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> (E.context -> T.term
    -> E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
    'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructors

  val ind_respects_variance_impl :
    E.global_env -> E.mutual_inductive_body -> Variance.t list -> E.context
    -> __ -> 'a1 ind_respects_variance -> 'a2 ind_respects_variance

  val on_variance_impl :
    E.global_env -> universes_decl -> Variance.t list option -> checker_flags
    -> checker_flags -> on_variance -> on_variance

  val on_global_env_impl_config :
    checker_flags -> checker_flags -> ((E.global_env, universes_decl) prod ->
    E.context -> T.term -> E.typ_or_sort -> ('a1, 'a3) on_global_env -> ('a2,
    'a4) on_global_env -> 'a3 -> 'a4) -> ((E.global_env, universes_decl) prod
    -> E.context -> T.term -> T.term -> conv_pb -> ('a1, 'a3) on_global_env
    -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) -> E.global_env -> ('a1, 'a3)
    on_global_env -> ('a2, 'a4) on_global_env

  val on_global_env_impl :
    checker_flags -> ((E.global_env, universes_decl) prod -> E.context ->
    T.term -> E.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env -> 'a2 -> 'a3) -> E.global_env -> ('a1, 'a2) on_global_env
    -> ('a1, 'a3) on_global_env
 end) ->
 sig
  type isType = Ty.typing ET.infer_sort

  type 'p coq_Forall_decls_typing =
    (CS.cumul_gen, 'p ET.lift_typing) GM.on_global_env

  type type_local_decl = __

  val refine_type :
    checker_flags -> E.global_env_ext -> E.context -> T.term -> T.term ->
    T.term -> Ty.typing -> Ty.typing

  type wf_local_rel = Ty.typing ET.lift_typing ET.coq_All_local_rel

  val on_wf_global_env_impl_config :
    checker_flags -> checker_flags -> checker_flags -> E.global_env ->
    (CS.cumul_gen, Ty.typing ET.lift_typing) GM.on_global_env ->
    (E.global_env_ext -> E.context -> conv_pb -> T.term -> T.term ->
    CS.cumul_gen -> CS.cumul_gen) -> ((E.global_env, universes_decl) prod ->
    E.context -> T.term -> E.typ_or_sort -> (CS.cumul_gen, Ty.typing
    ET.lift_typing) GM.on_global_env -> (CS.cumul_gen, 'a1) GM.on_global_env
    -> (CS.cumul_gen, 'a2) GM.on_global_env -> 'a1 -> 'a2) -> (CS.cumul_gen,
    'a1) GM.on_global_env -> (CS.cumul_gen, 'a2) GM.on_global_env

  val on_wf_global_env_impl :
    checker_flags -> E.global_env -> (CS.cumul_gen, Ty.typing ET.lift_typing)
    GM.on_global_env -> ((E.global_env, universes_decl) prod -> E.context ->
    T.term -> E.typ_or_sort -> (CS.cumul_gen, Ty.typing ET.lift_typing)
    GM.on_global_env -> (CS.cumul_gen, 'a1) GM.on_global_env ->
    (CS.cumul_gen, 'a2) GM.on_global_env -> 'a1 -> 'a2) -> (CS.cumul_gen,
    'a1) GM.on_global_env -> (CS.cumul_gen, 'a2) GM.on_global_env
 end
