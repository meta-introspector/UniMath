open All_Forall
open BasicAst
open Bool
open CRelationClasses
open Classes
open Datatypes
open Kernames
open List
open MCList
open MCOption
open MCProd
open Nat
open Primitive
open ReflectEq
open Signature
open Specif
open Universes

type __ = Obj.t

module type Term =
 sig
  type term

  val tRel : nat -> term

  val tSort : Universe.t -> term

  val tProd : aname -> term -> term -> term

  val tLambda : aname -> term -> term -> term

  val tLetIn : aname -> term -> term -> term -> term

  val tInd : inductive -> Instance.t -> term

  val tProj : projection -> term -> term

  val mkApps : term -> term list -> term

  val lift : nat -> nat -> term -> term

  val subst : term list -> nat -> term -> term

  val closedn : nat -> term -> bool

  val noccur_between : nat -> nat -> term -> bool

  val subst_instance_constr : term coq_UnivSubst
 end

module type TermDecide =
 functor (T:Term) ->
 sig
  val term_eq_dec : T.term coq_EqDec
 end

module TermDecideReflectInstances :
 functor (T:Term) ->
 functor (TDec:sig
  val term_eq_dec : T.term coq_EqDec
 end) ->
 sig
 end

module Retroknowledge :
 sig
  type t = { retro_int63 : kername option; retro_float64 : kername option }

  val retro_int63 : t -> kername option

  val retro_float64 : t -> kername option

  val empty : t

  val extendsb : t -> t -> bool

  val extendsT : t -> t -> reflect

  val reflect_t : t coq_ReflectEq

  val merge : t -> t -> t

  val compatible : t -> t -> bool
 end

module Environment :
 functor (T:Term) ->
 sig
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
                      retroknowledge : Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Retroknowledge.t

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
 end

module type EnvironmentSig =
 functor (T:Term) ->
 sig
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
                      retroknowledge : Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Retroknowledge.t

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
 end

module type EnvironmentDecide =
 functor (T:Term) ->
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
                      retroknowledge : Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Retroknowledge.t

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
  val context_eq_dec : E.context coq_EqDec

  val constructor_body_eq_dec : E.constructor_body coq_EqDec

  val projection_body_eq_dec : E.projection_body coq_EqDec

  val one_inductive_body_eq_dec : E.one_inductive_body coq_EqDec

  val mutual_inductive_body_eq_dec : E.mutual_inductive_body coq_EqDec

  val constant_body_eq_dec : E.constant_body coq_EqDec

  val global_decl_eq_dec : E.global_decl coq_EqDec
 end

module EnvironmentDecideReflectInstances :
 functor (T:Term) ->
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
                      retroknowledge : Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Retroknowledge.t

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
 functor (EDec:sig
  val context_eq_dec : E.context coq_EqDec

  val constructor_body_eq_dec : E.constructor_body coq_EqDec

  val projection_body_eq_dec : E.projection_body coq_EqDec

  val one_inductive_body_eq_dec : E.one_inductive_body coq_EqDec

  val mutual_inductive_body_eq_dec : E.mutual_inductive_body coq_EqDec

  val constant_body_eq_dec : E.constant_body coq_EqDec

  val global_decl_eq_dec : E.global_decl coq_EqDec
 end) ->
 sig
 end

module type TermUtils =
 functor (T:Term) ->
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
                      retroknowledge : Retroknowledge.t }

  val universes : global_env -> ContextSet.t

  val declarations : global_env -> global_declarations

  val retroknowledge : global_env -> Retroknowledge.t

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
  val destArity : E.context -> T.term -> (E.context, Universe.t) prod option

  val inds : kername -> Instance.t -> E.one_inductive_body list -> T.term list
 end
