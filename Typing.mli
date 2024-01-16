open All_Forall
open Ast
open AstUtils
open BasicAst
open BinNums
open Bool
open CRelationClasses
open Classes
open Datatypes
open EnvironmentTyping
open Kernames
open List
open MCList
open MCOption
open MCProd
open Nat
open PrimFloat
open PrimInt63
open Reflect
open ReflectEq
open Signature
open Specif
open TermEquality
open Universes
open Config

type __ = Obj.t

val isSort : term -> bool

val isArity : term -> bool

val type_of_constructor :
  Env.mutual_inductive_body -> Env.constructor_body -> (inductive, nat) prod
  -> Level.t list -> term

val fix_subst : term mfixpoint -> term list

val unfold_fix : term mfixpoint -> nat -> (nat, term) prod option

val cofix_subst : term mfixpoint -> term list

val unfold_cofix : term mfixpoint -> nat -> (nat, term) prod option

val is_constructor : nat -> term list -> bool

val fix_context : term mfixpoint -> Env.context

val dummy_branch : term branch

val iota_red : nat -> term list -> Env.context -> term branch -> term

val instantiate_params_subst_spec_sig_pack :
  Env.context -> term list -> term list -> term -> term list -> term ->
  (Env.context * (term list * (term list * (term * (term list * term))))) * __

val instantiate_params_subst_spec_Signature :
  Env.context -> term list -> term list -> term -> term list -> term ->
  (Env.context * (term list * (term list * (term * (term list * term))))) * __

val instantiate_params_subst :
  Env.context -> term list -> term list -> term -> (term list, term) prod
  option

type red1 =
| Coq_red_beta of aname * term * term * term * term list
| Coq_red_zeta of aname * term * term * term
| Coq_red_rel of nat * term
| Coq_red_iota of case_info * Env.mutual_inductive_body
   * Env.one_inductive_body * Env.constructor_body * nat * Instance.t
   * term list * term predicate * term branch list * term branch
| Coq_red_fix of term mfixpoint * nat * term list * nat * term
| Coq_red_cofix_case of case_info * term predicate * term mfixpoint * 
   nat * term list * nat * term * term branch list
| Coq_red_cofix_proj of projection * term mfixpoint * nat * term list * 
   nat * term
| Coq_red_delta of kername * Env.constant_body * term * Instance.t
| Coq_red_proj of projection * Instance.t * term list * term
| Coq_abs_red_l of aname * term * term * term * red1
| Coq_abs_red_r of aname * term * term * term * red1
| Coq_letin_red_def of aname * term * term * term * term * red1
| Coq_letin_red_ty of aname * term * term * term * term * red1
| Coq_letin_red_body of aname * term * term * term * term * red1
| Coq_case_red_pred_param of case_info * term list * term list * Instance.t
   * aname list * term * term * term branch list * (term, red1) coq_OnOne2
| Coq_case_red_pred_return of case_info * Env.mutual_inductive_body
   * Env.one_inductive_body * term list * Instance.t * aname list * term
   * term * term * term branch list * red1
| Coq_case_red_discr of case_info * term predicate * term * term
   * term branch list * red1
| Coq_case_red_brs of case_info * Env.mutual_inductive_body
   * Env.one_inductive_body * term predicate * term * term branch list
   * term branch list
   * (term branch, Env.context, (red1, __) prod) coq_OnOne2All
| Coq_proj_red of projection * term * term * red1
| Coq_app_red_l of term * term * term list * red1
| Coq_app_red_r of term list * term list * term * (term, red1) coq_OnOne2
| Coq_prod_red_l of aname * term * term * term * red1
| Coq_prod_red_r of aname * term * term * term * red1
| Coq_evar_red of nat * term list * term list * (term, red1) coq_OnOne2
| Coq_cast_red_l of term * cast_kind * term * term * red1
| Coq_cast_red_r of term * cast_kind * term * term * red1
| Coq_cast_red of term * cast_kind * term
| Coq_fix_red_ty of term def list * term def list * nat
   * (term def, (red1, __) prod) coq_OnOne2
| Coq_fix_red_body of term mfixpoint * term def list * nat
   * (term def, (red1, __) prod) coq_OnOne2
| Coq_cofix_red_ty of term def list * term def list * nat
   * (term def, (red1, __) prod) coq_OnOne2
| Coq_cofix_red_body of term mfixpoint * term def list * nat
   * (term def, (red1, __) prod) coq_OnOne2

val red1_rect :
  Env.global_env -> (Env.context -> aname -> term -> term -> term -> term
  list -> 'a1) -> (Env.context -> aname -> term -> term -> term -> 'a1) ->
  (Env.context -> nat -> term -> __ -> 'a1) -> (Env.context -> case_info ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> Env.constructor_body
  -> nat -> Instance.t -> term list -> term predicate -> term branch list ->
  term branch -> __ -> __ -> __ -> 'a1) -> (Env.context -> term mfixpoint ->
  nat -> term list -> nat -> term -> __ -> __ -> 'a1) -> (Env.context ->
  case_info -> term predicate -> term mfixpoint -> nat -> term list -> nat ->
  term -> term branch list -> __ -> 'a1) -> (Env.context -> projection ->
  term mfixpoint -> nat -> term list -> nat -> term -> __ -> 'a1) ->
  (Env.context -> kername -> Env.constant_body -> term -> __ -> Instance.t ->
  __ -> 'a1) -> (Env.context -> projection -> Instance.t -> term list -> term
  -> __ -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 ->
  'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1
  -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term -> red1 ->
  'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term ->
  red1 -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term ->
  term -> red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term list ->
  term list -> Instance.t -> aname list -> term -> term -> term branch list
  -> (term, red1) coq_OnOne2 -> 'a1) -> (Env.context -> case_info ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> term list ->
  Instance.t -> aname list -> term -> term -> term -> term branch list ->
  red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term predicate -> term
  -> term -> term branch list -> red1 -> 'a1 -> 'a1) -> (Env.context ->
  case_info -> Env.mutual_inductive_body -> Env.one_inductive_body -> __ ->
  term predicate -> term -> term branch list -> term branch list -> (term
  branch, Env.context, (red1, __) prod) coq_OnOne2All -> 'a1) -> (Env.context
  -> projection -> term -> term -> red1 -> 'a1 -> 'a1) -> (Env.context ->
  term -> term -> term list -> red1 -> 'a1 -> 'a1) -> (Env.context -> term
  list -> term list -> term -> (term, red1) coq_OnOne2 -> 'a1) ->
  (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 -> 'a1) ->
  (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 -> 'a1) ->
  (Env.context -> nat -> term list -> term list -> (term, red1) coq_OnOne2 ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> term -> red1 -> 'a1 ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> term -> red1 -> 'a1 ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> 'a1) -> (Env.context
  -> term def list -> term def list -> nat -> (term def, (red1, __) prod)
  coq_OnOne2 -> 'a1) -> (Env.context -> term mfixpoint -> term def list ->
  nat -> (term def, (red1, __) prod) coq_OnOne2 -> 'a1) -> (Env.context ->
  term def list -> term def list -> nat -> (term def, (red1, __) prod)
  coq_OnOne2 -> 'a1) -> (Env.context -> term mfixpoint -> term def list ->
  nat -> (term def, (red1, __) prod) coq_OnOne2 -> 'a1) -> Env.context ->
  term -> term -> red1 -> 'a1

val red1_rec :
  Env.global_env -> (Env.context -> aname -> term -> term -> term -> term
  list -> 'a1) -> (Env.context -> aname -> term -> term -> term -> 'a1) ->
  (Env.context -> nat -> term -> __ -> 'a1) -> (Env.context -> case_info ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> Env.constructor_body
  -> nat -> Instance.t -> term list -> term predicate -> term branch list ->
  term branch -> __ -> __ -> __ -> 'a1) -> (Env.context -> term mfixpoint ->
  nat -> term list -> nat -> term -> __ -> __ -> 'a1) -> (Env.context ->
  case_info -> term predicate -> term mfixpoint -> nat -> term list -> nat ->
  term -> term branch list -> __ -> 'a1) -> (Env.context -> projection ->
  term mfixpoint -> nat -> term list -> nat -> term -> __ -> 'a1) ->
  (Env.context -> kername -> Env.constant_body -> term -> __ -> Instance.t ->
  __ -> 'a1) -> (Env.context -> projection -> Instance.t -> term list -> term
  -> __ -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 ->
  'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1
  -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term -> red1 ->
  'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term ->
  red1 -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term ->
  term -> red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term list ->
  term list -> Instance.t -> aname list -> term -> term -> term branch list
  -> (term, red1) coq_OnOne2 -> 'a1) -> (Env.context -> case_info ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> term list ->
  Instance.t -> aname list -> term -> term -> term -> term branch list ->
  red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term predicate -> term
  -> term -> term branch list -> red1 -> 'a1 -> 'a1) -> (Env.context ->
  case_info -> Env.mutual_inductive_body -> Env.one_inductive_body -> __ ->
  term predicate -> term -> term branch list -> term branch list -> (term
  branch, Env.context, (red1, __) prod) coq_OnOne2All -> 'a1) -> (Env.context
  -> projection -> term -> term -> red1 -> 'a1 -> 'a1) -> (Env.context ->
  term -> term -> term list -> red1 -> 'a1 -> 'a1) -> (Env.context -> term
  list -> term list -> term -> (term, red1) coq_OnOne2 -> 'a1) ->
  (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 -> 'a1) ->
  (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 -> 'a1) ->
  (Env.context -> nat -> term list -> term list -> (term, red1) coq_OnOne2 ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> term -> red1 -> 'a1 ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> term -> red1 -> 'a1 ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> 'a1) -> (Env.context
  -> term def list -> term def list -> nat -> (term def, (red1, __) prod)
  coq_OnOne2 -> 'a1) -> (Env.context -> term mfixpoint -> term def list ->
  nat -> (term def, (red1, __) prod) coq_OnOne2 -> 'a1) -> (Env.context ->
  term def list -> term def list -> nat -> (term def, (red1, __) prod)
  coq_OnOne2 -> 'a1) -> (Env.context -> term mfixpoint -> term def list ->
  nat -> (term def, (red1, __) prod) coq_OnOne2 -> 'a1) -> Env.context ->
  term -> term -> red1 -> 'a1

val red1_ind_all :
  Env.global_env -> (Env.context -> aname -> term -> term -> term -> term
  list -> 'a1) -> (Env.context -> aname -> term -> term -> term -> 'a1) ->
  (Env.context -> nat -> term -> __ -> 'a1) -> (Env.context -> case_info ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> Env.constructor_body
  -> nat -> Instance.t -> term list -> term predicate -> term branch list ->
  term branch -> __ -> __ -> __ -> 'a1) -> (Env.context -> term mfixpoint ->
  nat -> term list -> nat -> term -> __ -> __ -> 'a1) -> (Env.context ->
  case_info -> term predicate -> term mfixpoint -> nat -> term list -> nat ->
  term -> term branch list -> __ -> 'a1) -> (Env.context -> projection ->
  term mfixpoint -> nat -> term list -> nat -> term -> __ -> 'a1) ->
  (Env.context -> kername -> Env.constant_body -> term -> __ -> Instance.t ->
  __ -> 'a1) -> (Env.context -> projection -> term list -> Instance.t -> term
  -> __ -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 ->
  'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1
  -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term -> red1 ->
  'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term ->
  red1 -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term ->
  term -> red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term list ->
  term list -> Instance.t -> aname list -> term -> term -> term branch list
  -> (term, (red1, 'a1) prod) coq_OnOne2 -> 'a1) -> (Env.context -> case_info
  -> Env.one_inductive_body -> Env.mutual_inductive_body -> __ -> term list
  -> Instance.t -> aname list -> term -> term -> term -> term branch list ->
  red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term predicate -> term
  -> term -> term branch list -> red1 -> 'a1 -> 'a1) -> (Env.context ->
  case_info -> Env.mutual_inductive_body -> Env.one_inductive_body -> __ ->
  term predicate -> term -> term branch list -> term branch list -> (term
  branch, Env.context, ((red1, 'a1) prod, __) prod) coq_OnOne2All -> 'a1) ->
  (Env.context -> projection -> term -> term -> red1 -> 'a1 -> 'a1) ->
  (Env.context -> term -> term -> term list -> red1 -> 'a1 -> 'a1) ->
  (Env.context -> term list -> term list -> term -> (term, (red1, 'a1) prod)
  coq_OnOne2 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1
  -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 ->
  'a1 -> 'a1) -> (Env.context -> nat -> term list -> term list -> (term,
  (red1, 'a1) prod) coq_OnOne2 -> 'a1) -> (Env.context -> term -> cast_kind
  -> term -> term -> red1 -> 'a1 -> 'a1) -> (Env.context -> term -> cast_kind
  -> term -> term -> red1 -> 'a1 -> 'a1) -> (Env.context -> term -> cast_kind
  -> term -> 'a1) -> (Env.context -> term def list -> term def list -> nat ->
  (term def, ((red1, 'a1) prod, __) prod) coq_OnOne2 -> 'a1) -> (Env.context
  -> term def list -> term def list -> nat -> (term def, ((red1, 'a1) prod,
  __) prod) coq_OnOne2 -> 'a1) -> (Env.context -> term def list -> term def
  list -> nat -> (term def, ((red1, 'a1) prod, __) prod) coq_OnOne2 -> 'a1)
  -> (Env.context -> term def list -> term def list -> nat -> (term def,
  ((red1, 'a1) prod, __) prod) coq_OnOne2 -> 'a1) -> Env.context -> term ->
  term -> red1 -> 'a1

type red =
| Coq_refl_red
| Coq_trans_red of term * term * red * red1

val red_rect :
  Env.global_env -> Env.context -> term -> 'a1 -> (term -> term -> red -> 'a1
  -> red1 -> 'a1) -> term -> red -> 'a1

val red_rec :
  Env.global_env -> Env.context -> term -> 'a1 -> (term -> term -> red -> 'a1
  -> red1 -> 'a1) -> term -> red -> 'a1

type eq_term_nocast = compare_term

type leq_term_nocast = compare_term

module Coq__1 : sig
 type cumul_gen =
 | Coq_cumul_refl of term * term * compare_term
 | Coq_cumul_red_l of term * term * term * red1 * cumul_gen
 | Coq_cumul_red_r of term * term * term * cumul_gen * red1
end
include module type of struct include Coq__1 end

val cumul_gen_rect :
  checker_flags -> Env.global_env_ext -> Env.context -> conv_pb -> (term ->
  term -> compare_term -> 'a1) -> (term -> term -> term -> red1 -> cumul_gen
  -> 'a1 -> 'a1) -> (term -> term -> term -> cumul_gen -> 'a1 -> red1 -> 'a1)
  -> term -> term -> cumul_gen -> 'a1

val cumul_gen_rec :
  checker_flags -> Env.global_env_ext -> Env.context -> conv_pb -> (term ->
  term -> compare_term -> 'a1) -> (term -> term -> term -> red1 -> cumul_gen
  -> 'a1 -> 'a1) -> (term -> term -> term -> cumul_gen -> 'a1 -> red1 -> 'a1)
  -> term -> term -> cumul_gen -> 'a1

val conv_refl' :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> cumul_gen

val cumul_refl' :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> cumul_gen

type eq_opt_term = __

type eq_decl = (eq_opt_term, compare_term) prod

type eq_context = (term context_decl, term context_decl, eq_decl) coq_All2

module TemplateEnvTyping :
 sig
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of Env.context * aname * term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of Env.context * aname * term * term
     * 'typing coq_All_local_env * 'typing * 'typing

  val coq_All_local_env_rect :
    'a2 -> (Env.context -> aname -> term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (Env.context -> aname -> term -> term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> Env.context -> 'a1
    coq_All_local_env -> 'a2

  val coq_All_local_env_rec :
    'a2 -> (Env.context -> aname -> term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (Env.context -> aname -> term -> term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> Env.context -> 'a1
    coq_All_local_env -> 'a2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  val coq_All_local_env_sig_pack :
    Env.context -> 'a1 coq_All_local_env -> Env.context * 'a1
    coq_All_local_env

  val coq_All_local_env_Signature :
    Env.context -> ('a1 coq_All_local_env, Env.context, 'a1
    coq_All_local_env_sig) coq_Signature

  val coq_NoConfusionPackage_All_local_env :
    (Env.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

  val coq_All_local_env_fold :
    (nat -> term -> term) -> Env.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT

  val coq_All_local_env_impl :
    Env.context -> 'a1 coq_All_local_env -> (Env.context -> term ->
    Env.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

  val coq_All_local_env_impl_ind :
    Env.context -> 'a1 coq_All_local_env -> (Env.context -> term ->
    Env.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env

  val coq_All_local_env_skipn :
    Env.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

  type 'p coq_All_local_rel = 'p coq_All_local_env

  val coq_All_local_rel_nil : Env.context -> 'a1 coq_All_local_rel

  val coq_All_local_rel_abs :
    Env.context -> Env.context -> term -> aname -> 'a1 coq_All_local_rel ->
    'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_def :
    Env.context -> Env.context -> term -> term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

  val coq_All_local_rel_local :
    Env.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

  val coq_All_local_local_rel :
    Env.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

  val coq_All_local_app_rel :
    Env.context -> Env.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_rel) prod

  val coq_All_local_rel_app :
    Env.context -> Env.context -> 'a1 coq_All_local_env -> 'a1
    coq_All_local_rel -> 'a1 coq_All_local_env

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  val lift_judgment_impl :
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> Env.typ_or_sort -> ('a1, 'a2) lift_judgment -> (term ->
    'a1 -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  val infer_sort_impl :
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 ->
    'a2) -> 'a2 infer_sort

  val infer_typing_sort_impl :
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 ->
    'a2) -> 'a2 infer_sort

  val lift_typing_impl :
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> Env.typ_or_sort -> 'a1 lift_typing -> (term -> 'a1 ->
    'a2) -> 'a2 lift_typing

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen =
  | Coq_localenv_over_nil
  | Coq_localenv_over_cons_abs of Env.context * aname * term
     * ('checking, 'sorting) lift_judgment coq_All_local_env
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
     * 'sproperty
  | Coq_localenv_over_cons_def of Env.context * aname * term * term
     * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
     * ('checking, 'sorting, 'cproperty, 'sproperty)
       coq_All_local_env_over_gen * 'cproperty
     * ('checking, 'sorting) lift_judgment * 'sproperty

  val coq_All_local_env_over_gen_rect :
    Env.global_env_ext -> 'a5 -> (Env.context -> aname -> term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (Env.context -> aname -> term -> term -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> Env.context -> ('a1, 'a2) lift_judgment coq_All_local_env
    -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  val coq_All_local_env_over_gen_rec :
    Env.global_env_ext -> 'a5 -> (Env.context -> aname -> term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (Env.context -> aname -> term -> term -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> Env.context -> ('a1, 'a2) lift_judgment coq_All_local_env
    -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_sig_pack :
    Env.global_env_ext -> Env.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (Env.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen

  val coq_All_local_env_over_gen_Signature :
    Env.global_env_ext -> Env.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    Env.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature

  type ('typing, 'property) coq_All_local_env_over =
    ('typing, 'typing infer_sort, 'property, 'property)
    coq_All_local_env_over_gen

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
    ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
    coq_All_local_env_over_gen

  type 'typing ctx_inst =
  | Coq_ctx_inst_nil
  | Coq_ctx_inst_ass of aname * term * term * term list * Env.context
     * 'typing * 'typing ctx_inst
  | Coq_ctx_inst_def of aname * term * term * term list * Env.context
     * 'typing ctx_inst

  val ctx_inst_rect :
    Env.global_env_ext -> Env.context -> 'a2 -> (aname -> term -> term ->
    term list -> Env.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> term -> term -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> term list -> Env.context -> 'a1 ctx_inst -> 'a2

  val ctx_inst_rec :
    Env.global_env_ext -> Env.context -> 'a2 -> (aname -> term -> term ->
    term list -> Env.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> term -> term -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> term list -> Env.context -> 'a1 ctx_inst -> 'a2

  type 'typing ctx_inst_sig = 'typing ctx_inst

  val ctx_inst_sig_pack :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
    ctx_inst -> (term list * Env.context) * 'a1 ctx_inst

  val ctx_inst_Signature :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> ('a1
    ctx_inst, term list * Env.context, 'a1 ctx_inst_sig) coq_Signature

  val coq_NoConfusionPackage_ctx_inst :
    Env.global_env_ext -> Env.context -> ((term list * Env.context) * 'a1
    ctx_inst) coq_NoConfusionPackage

  val ctx_inst_impl_gen :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> __ list
    -> (__, __ ctx_inst) sigT -> (term -> term -> (__, __) coq_All -> 'a1) ->
    (__, __ ctx_inst) coq_All -> 'a1 ctx_inst

  val ctx_inst_impl :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
    ctx_inst -> (term -> term -> 'a1 -> 'a2) -> 'a2 ctx_inst

  val coq_All_local_env_size_gen :
    (Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> 'a1 ->
    size) -> size -> Env.global_env_ext -> Env.context -> 'a1
    coq_All_local_env -> size

  val lift_judgment_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> 'a2 -> size) ->
    Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1,
    'a2) lift_judgment -> size

  val lift_typing_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size

  val coq_All_local_env_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    Env.global_env_ext -> Env.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size

  val coq_All_local_rel_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    Env.global_env_ext -> Env.context -> Env.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size

  val lift_sorting_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size)
    -> Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1,
    'a2 infer_sort) lift_judgment -> size

  val coq_All_local_env_sorting_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size)
    -> Env.global_env_ext -> Env.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_env -> size

  val coq_All_local_rel_sorting_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size)
    -> Env.global_env_ext -> Env.context -> Env.context -> ('a1, 'a2
    infer_sort) lift_judgment coq_All_local_rel -> size
 end

type 'typing coq_All_local_env = 'typing TemplateEnvTyping.coq_All_local_env =
| Coq_localenv_nil
| Coq_localenv_cons_abs of Env.context * aname * term
   * 'typing coq_All_local_env * 'typing
| Coq_localenv_cons_def of Env.context * aname * term * term
   * 'typing coq_All_local_env * 'typing * 'typing

val coq_All_local_env_rect :
  'a2 -> (Env.context -> aname -> term -> 'a1 coq_All_local_env -> 'a2 -> 'a1
  -> 'a2) -> (Env.context -> aname -> term -> term -> 'a1 coq_All_local_env
  -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> Env.context -> 'a1 coq_All_local_env -> 'a2

val coq_All_local_env_rec :
  'a2 -> (Env.context -> aname -> term -> 'a1 coq_All_local_env -> 'a2 -> 'a1
  -> 'a2) -> (Env.context -> aname -> term -> term -> 'a1 coq_All_local_env
  -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> Env.context -> 'a1 coq_All_local_env -> 'a2

type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

val coq_All_local_env_sig_pack :
  Env.context -> 'a1 coq_All_local_env -> Env.context * 'a1 coq_All_local_env

val coq_All_local_env_Signature :
  Env.context -> ('a1 coq_All_local_env, Env.context, 'a1
  coq_All_local_env_sig) coq_Signature

val coq_NoConfusionPackage_All_local_env :
  (Env.context * 'a1 coq_All_local_env) coq_NoConfusionPackage

val coq_All_local_env_fold :
  (nat -> term -> term) -> Env.context -> ('a1 coq_All_local_env, 'a1
  coq_All_local_env) iffT

val coq_All_local_env_impl :
  Env.context -> 'a1 coq_All_local_env -> (Env.context -> term ->
  Env.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

val coq_All_local_env_impl_ind :
  Env.context -> 'a1 coq_All_local_env -> (Env.context -> term ->
  Env.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
  coq_All_local_env

val coq_All_local_env_skipn :
  Env.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

type 'p coq_All_local_rel = 'p coq_All_local_env

val coq_All_local_rel_nil : Env.context -> 'a1 coq_All_local_rel

val coq_All_local_rel_abs :
  Env.context -> Env.context -> term -> aname -> 'a1 coq_All_local_rel -> 'a1
  -> 'a1 coq_All_local_rel

val coq_All_local_rel_def :
  Env.context -> Env.context -> term -> term -> aname -> 'a1
  coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

val coq_All_local_rel_local :
  Env.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel

val coq_All_local_local_rel :
  Env.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

val coq_All_local_app_rel :
  Env.context -> Env.context -> 'a1 coq_All_local_env -> ('a1
  coq_All_local_env, 'a1 coq_All_local_rel) prod

val coq_All_local_rel_app :
  Env.context -> Env.context -> 'a1 coq_All_local_env -> 'a1
  coq_All_local_rel -> 'a1 coq_All_local_env

type 'p on_local_decl = __

type 'p on_def_type = 'p

type 'p on_def_body = 'p

type ('check, 'infer_sort) lift_judgment = __

val lift_judgment_impl :
  Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
  term -> term -> Env.typ_or_sort -> ('a1, 'a2) lift_judgment -> (term -> 'a1
  -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

type 'wf_term lift_wf_term =
  (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

type 'sorting infer_sort = (Universe.t, 'sorting) sigT

type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

type ('checking, 'sorting) lift_sorting =
  ('checking, 'sorting infer_sort) lift_judgment

type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

val infer_sort_impl :
  Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
  term -> term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 ->
  'a2) -> 'a2 infer_sort

val infer_typing_sort_impl :
  Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
  term -> term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 ->
  'a2) -> 'a2 infer_sort

val lift_typing_impl :
  Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
  term -> term -> Env.typ_or_sort -> 'a1 lift_typing -> (term -> 'a1 -> 'a2)
  -> 'a2 lift_typing

type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen = (
'checking, 'sorting, 'cproperty, 'sproperty) TemplateEnvTyping.coq_All_local_env_over_gen =
| Coq_localenv_over_nil
| Coq_localenv_over_cons_abs of Env.context * aname * term
   * ('checking, 'sorting) lift_judgment coq_All_local_env
   * ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen
   * ('checking, 'sorting) lift_judgment * 'sproperty
| Coq_localenv_over_cons_def of Env.context * aname * term * term
   * ('checking, 'sorting) lift_judgment coq_All_local_env * 'checking
   * ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen
   * 'cproperty * ('checking, 'sorting) lift_judgment * 'sproperty

val coq_All_local_env_over_gen_rect :
  Env.global_env_ext -> 'a5 -> (Env.context -> aname -> term -> ('a1, 'a2)
  lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
  coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
  'a5) -> (Env.context -> aname -> term -> term -> ('a1, 'a2) lift_judgment
  coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen
  -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment -> 'a4 -> 'a5) -> Env.context ->
  ('a1, 'a2) lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
  coq_All_local_env_over_gen -> 'a5

val coq_All_local_env_over_gen_rec :
  Env.global_env_ext -> 'a5 -> (Env.context -> aname -> term -> ('a1, 'a2)
  lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
  coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
  'a5) -> (Env.context -> aname -> term -> term -> ('a1, 'a2) lift_judgment
  coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen
  -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment -> 'a4 -> 'a5) -> Env.context ->
  ('a1, 'a2) lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
  coq_All_local_env_over_gen -> 'a5

type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
  ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

val coq_All_local_env_over_gen_sig_pack :
  Env.global_env_ext -> Env.context -> ('a1, 'a2) lift_judgment
  coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
  (Env.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
  'a3, 'a4) coq_All_local_env_over_gen

val coq_All_local_env_over_gen_Signature :
  Env.global_env_ext -> Env.context -> ('a1, 'a2) lift_judgment
  coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
  Env.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
  'a4) coq_All_local_env_over_gen_sig) coq_Signature

type ('typing, 'property) coq_All_local_env_over =
  ('typing, 'typing infer_sort, 'property, 'property)
  coq_All_local_env_over_gen

type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
  ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
  coq_All_local_env_over_gen

type 'typing ctx_inst = 'typing TemplateEnvTyping.ctx_inst =
| Coq_ctx_inst_nil
| Coq_ctx_inst_ass of aname * term * term * term list * Env.context * 
   'typing * 'typing ctx_inst
| Coq_ctx_inst_def of aname * term * term * term list * Env.context
   * 'typing ctx_inst

val ctx_inst_rect :
  Env.global_env_ext -> Env.context -> 'a2 -> (aname -> term -> term -> term
  list -> Env.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> term
  -> term -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 -> 'a2) -> term
  list -> Env.context -> 'a1 ctx_inst -> 'a2

val ctx_inst_rec :
  Env.global_env_ext -> Env.context -> 'a2 -> (aname -> term -> term -> term
  list -> Env.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> term
  -> term -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 -> 'a2) -> term
  list -> Env.context -> 'a1 ctx_inst -> 'a2

type 'typing ctx_inst_sig = 'typing ctx_inst

val ctx_inst_sig_pack :
  Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
  ctx_inst -> (term list * Env.context) * 'a1 ctx_inst

val ctx_inst_Signature :
  Env.global_env_ext -> Env.context -> term list -> Env.context -> ('a1
  ctx_inst, term list * Env.context, 'a1 ctx_inst_sig) coq_Signature

val coq_NoConfusionPackage_ctx_inst :
  Env.global_env_ext -> Env.context -> ((term list * Env.context) * 'a1
  ctx_inst) coq_NoConfusionPackage

val ctx_inst_impl_gen :
  Env.global_env_ext -> Env.context -> term list -> Env.context -> __ list ->
  (__, __ ctx_inst) sigT -> (term -> term -> (__, __) coq_All -> 'a1) -> (__,
  __ ctx_inst) coq_All -> 'a1 ctx_inst

val ctx_inst_impl :
  Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
  ctx_inst -> (term -> term -> 'a1 -> 'a2) -> 'a2 ctx_inst

val coq_All_local_env_size_gen :
  (Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> 'a1 ->
  size) -> size -> Env.global_env_ext -> Env.context -> 'a1 coq_All_local_env
  -> size

val lift_judgment_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  (Env.global_env_ext -> Env.context -> term -> 'a2 -> size) ->
  Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1, 'a2)
  lift_judgment -> size

val lift_typing_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1, 'a1
  infer_sort) lift_judgment -> size

val coq_All_local_env_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  Env.global_env_ext -> Env.context -> ('a1, 'a1 infer_sort) lift_judgment
  coq_All_local_env -> size

val coq_All_local_rel_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  Env.global_env_ext -> Env.context -> Env.context -> ('a1, 'a1 infer_sort)
  lift_judgment coq_All_local_rel -> size

val lift_sorting_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size) ->
  Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1, 'a2
  infer_sort) lift_judgment -> size

val coq_All_local_env_sorting_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size) ->
  Env.global_env_ext -> Env.context -> ('a1, 'a2 infer_sort) lift_judgment
  coq_All_local_env -> size

val coq_All_local_rel_sorting_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size) ->
  Env.global_env_ext -> Env.context -> Env.context -> ('a1, 'a2 infer_sort)
  lift_judgment coq_All_local_rel -> size

module TemplateConversion :
 sig
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot * 
     term * term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot * 
     term * term * term * term * 'p * 'p

  val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __
    -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __
    -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> term context_decl -> term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (term context_decl * term context_decl) * 'a1
    coq_All_decls_alpha_pb

  val coq_All_decls_alpha_pb_Signature :
    conv_pb -> term context_decl -> term context_decl -> ('a1
    coq_All_decls_alpha_pb, term context_decl * term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature

  val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((term context_decl * term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  val coq_All_decls_alpha_pb_impl :
    conv_pb -> term context_decl -> term context_decl -> (conv_pb -> term ->
    term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb
 end

type 'p coq_All_decls_alpha_pb = 'p TemplateConversion.coq_All_decls_alpha_pb =
| Coq_all_decls_alpha_vass of name binder_annot * name binder_annot * 
   term * term * 'p
| Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot * 
   term * term * term * term * 'p * 'p

val coq_All_decls_alpha_pb_rect :
  conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __ ->
  'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term ->
  term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
  context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

val coq_All_decls_alpha_pb_rec :
  conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __ ->
  'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term ->
  term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
  context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2

type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

val coq_All_decls_alpha_pb_sig_pack :
  conv_pb -> term context_decl -> term context_decl -> 'a1
  coq_All_decls_alpha_pb -> (term context_decl * term context_decl) * 'a1
  coq_All_decls_alpha_pb

val coq_All_decls_alpha_pb_Signature :
  conv_pb -> term context_decl -> term context_decl -> ('a1
  coq_All_decls_alpha_pb, term context_decl * term context_decl, 'a1
  coq_All_decls_alpha_pb_sig) coq_Signature

val coq_NoConfusionPackage_All_decls_alpha_pb :
  conv_pb -> ((term context_decl * term context_decl) * 'a1
  coq_All_decls_alpha_pb) coq_NoConfusionPackage

type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

type 'cumul_gen cumul_pb_context =
  (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

type 'cumul_gen cumul_ctx_rel =
  (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

val coq_All_decls_alpha_pb_impl :
  conv_pb -> term context_decl -> term context_decl -> (conv_pb -> term ->
  term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
  coq_All_decls_alpha_pb

module TemplateGlobalMaps :
 sig
  type 'p on_context = 'p TemplateEnvTyping.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t

  val ind_realargs : Env.one_inductive_body -> nat

  type positive_cstr_arg =
  | Coq_pos_arg_closed of term
  | Coq_pos_arg_concl of term list * nat * Env.one_inductive_body
     * (term, __) coq_All
  | Coq_pos_arg_let of aname * term * term * term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * term * term * positive_cstr_arg

  val positive_cstr_arg_rect :
    Env.mutual_inductive_body -> (term context_decl list -> term -> __ ->
    'a1) -> (term context_decl list -> term list -> nat ->
    Env.one_inductive_body -> __ -> (term, __) coq_All -> __ -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> term -> positive_cstr_arg
    -> 'a1 -> 'a1) -> (term context_decl list -> aname -> term -> term -> __
    -> positive_cstr_arg -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr_arg -> 'a1

  val positive_cstr_arg_rec :
    Env.mutual_inductive_body -> (term context_decl list -> term -> __ ->
    'a1) -> (term context_decl list -> term list -> nat ->
    Env.one_inductive_body -> __ -> (term, __) coq_All -> __ -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> term -> positive_cstr_arg
    -> 'a1 -> 'a1) -> (term context_decl list -> aname -> term -> term -> __
    -> positive_cstr_arg -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr_arg -> 'a1

  type positive_cstr =
  | Coq_pos_concl of term list * (term, __) coq_All
  | Coq_pos_let of aname * term * term * term * positive_cstr
  | Coq_pos_ass of aname * term * term * positive_cstr_arg * positive_cstr

  val positive_cstr_rect :
    Env.mutual_inductive_body -> nat -> (term context_decl list -> term list
    -> (term, __) coq_All -> 'a1) -> (term context_decl list -> aname -> term
    -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term context_decl
    list -> aname -> term -> term -> positive_cstr_arg -> positive_cstr ->
    'a1 -> 'a1) -> term context_decl list -> term -> positive_cstr -> 'a1

  val positive_cstr_rec :
    Env.mutual_inductive_body -> nat -> (term context_decl list -> term list
    -> (term, __) coq_All -> 'a1) -> (term context_decl list -> aname -> term
    -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term context_decl
    list -> aname -> term -> term -> positive_cstr_arg -> positive_cstr ->
    'a1 -> 'a1) -> term context_decl list -> term -> positive_cstr -> 'a1

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

  val ind_arities : Env.mutual_inductive_body -> term context_decl list

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  val cstr_concl_head :
    Env.mutual_inductive_body -> nat -> Env.constructor_body -> term

  val cstr_concl :
    Env.mutual_inductive_body -> nat -> Env.constructor_body -> term

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p
                                                    TemplateEnvTyping.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  val on_ctype :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> 'a2 on_type

  val on_cargs :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx

  val on_cindices :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> 'a2
    TemplateEnvTyping.ctx_inst

  val on_ctype_positive :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> positive_cstr

  val on_ctype_variance :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
    cstr_respects_variance

  type ('pcmp, 'p) on_constructors =
    (Env.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor)
    coq_All2

  type on_projections =
    (Env.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  val on_projs :
    Env.mutual_inductive_body -> kername -> nat -> Env.one_inductive_body ->
    Env.context -> Env.constructor_body -> on_projections ->
    (Env.projection_body, __) coq_Alli

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
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> 'a2 on_type

  val ind_cunivs :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> constructor_univs list

  val onConstructors :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> ('a1, 'a2) on_constructors

  val onProjections :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> __

  val ind_sorts :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> 'a2 check_ind_sorts

  val onIndices :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> __

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (Env.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  val onInductives :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    (Env.one_inductive_body, ('a1, 'a2) on_ind_body) coq_Alli

  val onParams :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> ('a1, 'a2) on_inductive -> 'a2 on_context

  val onVariance :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> ('a1, 'a2) on_inductive -> on_variance

  type 'p on_constant_decl = __

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls_data -> universes_decl

  val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls_data -> ('a1, 'a2) on_global_decl

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of Env.global_declarations * kername * Env.global_decl
     * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

  val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    Env.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    Env.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> ('a1, 'a2) on_global_decls ->
    Env.global_declarations * ('a1, 'a2) on_global_decls

  val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> (('a1, 'a2) on_global_decls,
    Env.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature

  type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

  type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

  val type_local_ctx_impl_gen :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t -> __ list
    -> (__, __ type_local_ctx) sigT -> (Env.context -> term ->
    Env.typ_or_sort -> (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx)
    coq_All -> 'a1 type_local_ctx

  val type_local_ctx_impl :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t -> 'a1
    type_local_ctx -> (Env.context -> term -> Env.typ_or_sort -> 'a1 -> 'a2)
    -> 'a2 type_local_ctx

  val sorts_local_ctx_impl_gen :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t list -> __
    list -> (__, __ sorts_local_ctx) sigT -> (Env.context -> term ->
    Env.typ_or_sort -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx)
    coq_All -> 'a1 sorts_local_ctx

  val sorts_local_ctx_impl :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t list ->
    'a1 sorts_local_ctx -> (Env.context -> term -> Env.typ_or_sort -> 'a1 ->
    'a2) -> 'a2 sorts_local_ctx

  val cstr_respects_variance_impl_gen :
    Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
    Env.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT
    -> __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
    cstr_respects_variance

  val cstr_respects_variance_impl :
    Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
    Env.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
    cstr_respects_variance

  val on_constructor_impl_config_gen :
    Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
    Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (Env.context -> term -> Env.typ_or_sort -> (((checker_flags, __) prod,
    __) prod, __) coq_All -> 'a2) -> (universes_decl -> Env.context -> term
    -> term -> conv_pb -> (((checker_flags, __) prod, __) prod, __) coq_All
    -> 'a1) -> (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1,
    'a2) on_constructor

  val on_constructors_impl_config_gen :
    Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
    Env.one_inductive_body -> Env.context -> Env.constructor_body list ->
    Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> (Env.context -> term
    -> Env.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All
    -> 'a2) -> (universes_decl -> Env.context -> term -> term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructors

  val ind_respects_variance_impl :
    Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
    Env.context -> __ -> 'a1 ind_respects_variance -> 'a2
    ind_respects_variance

  val on_variance_impl :
    Env.global_env -> universes_decl -> Variance.t list option ->
    checker_flags -> checker_flags -> on_variance -> on_variance

  val on_global_env_impl_config :
    checker_flags -> checker_flags -> ((Env.global_env, universes_decl) prod
    -> Env.context -> term -> Env.typ_or_sort -> ('a1, 'a3) on_global_env ->
    ('a2, 'a4) on_global_env -> 'a3 -> 'a4) -> ((Env.global_env,
    universes_decl) prod -> Env.context -> term -> term -> conv_pb -> ('a1,
    'a3) on_global_env -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) ->
    Env.global_env -> ('a1, 'a3) on_global_env -> ('a2, 'a4) on_global_env

  val on_global_env_impl :
    checker_flags -> ((Env.global_env, universes_decl) prod -> Env.context ->
    term -> Env.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env -> 'a2 -> 'a3) -> Env.global_env -> ('a1, 'a2)
    on_global_env -> ('a1, 'a3) on_global_env
 end

type 'p on_context = 'p TemplateEnvTyping.coq_All_local_env

type 'p type_local_ctx = __

type 'p sorts_local_ctx = __

type 'p on_type = 'p

val univs_ext_constraints :
  ConstraintSet.t -> universes_decl -> ConstraintSet.t

val ind_realargs : Env.one_inductive_body -> nat

type positive_cstr_arg = TemplateGlobalMaps.positive_cstr_arg =
| Coq_pos_arg_closed of term
| Coq_pos_arg_concl of term list * nat * Env.one_inductive_body
   * (term, __) coq_All
| Coq_pos_arg_let of aname * term * term * term * positive_cstr_arg
| Coq_pos_arg_ass of aname * term * term * positive_cstr_arg

val positive_cstr_arg_rect :
  Env.mutual_inductive_body -> (term context_decl list -> term -> __ -> 'a1)
  -> (term context_decl list -> term list -> nat -> Env.one_inductive_body ->
  __ -> (term, __) coq_All -> __ -> 'a1) -> (term context_decl list -> aname
  -> term -> term -> term -> positive_cstr_arg -> 'a1 -> 'a1) -> (term
  context_decl list -> aname -> term -> term -> __ -> positive_cstr_arg ->
  'a1 -> 'a1) -> term context_decl list -> term -> positive_cstr_arg -> 'a1

val positive_cstr_arg_rec :
  Env.mutual_inductive_body -> (term context_decl list -> term -> __ -> 'a1)
  -> (term context_decl list -> term list -> nat -> Env.one_inductive_body ->
  __ -> (term, __) coq_All -> __ -> 'a1) -> (term context_decl list -> aname
  -> term -> term -> term -> positive_cstr_arg -> 'a1 -> 'a1) -> (term
  context_decl list -> aname -> term -> term -> __ -> positive_cstr_arg ->
  'a1 -> 'a1) -> term context_decl list -> term -> positive_cstr_arg -> 'a1

type positive_cstr = TemplateGlobalMaps.positive_cstr =
| Coq_pos_concl of term list * (term, __) coq_All
| Coq_pos_let of aname * term * term * term * positive_cstr
| Coq_pos_ass of aname * term * term * positive_cstr_arg * positive_cstr

val positive_cstr_rect :
  Env.mutual_inductive_body -> nat -> (term context_decl list -> term list ->
  (term, __) coq_All -> 'a1) -> (term context_decl list -> aname -> term ->
  term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term context_decl list ->
  aname -> term -> term -> positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1)
  -> term context_decl list -> term -> positive_cstr -> 'a1

val positive_cstr_rec :
  Env.mutual_inductive_body -> nat -> (term context_decl list -> term list ->
  (term, __) coq_All -> 'a1) -> (term context_decl list -> aname -> term ->
  term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term context_decl list ->
  aname -> term -> term -> positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1)
  -> term context_decl list -> term -> positive_cstr -> 'a1

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
  universes_decl -> Variance.t list -> ((universes_decl, Level.t_ list) prod,
  Level.t_ list) prod option

val ind_arities : Env.mutual_inductive_body -> term context_decl list

type 'pcmp ind_respects_variance = __

type 'pcmp cstr_respects_variance = __

val cstr_concl_head :
  Env.mutual_inductive_body -> nat -> Env.constructor_body -> term

val cstr_concl :
  Env.mutual_inductive_body -> nat -> Env.constructor_body -> term

type ('pcmp, 'p) on_constructor = ('pcmp, 'p) TemplateGlobalMaps.on_constructor = { 
on_ctype : 'p on_type; on_cargs : 'p sorts_local_ctx;
on_cindices : 'p TemplateEnvTyping.ctx_inst;
on_ctype_positive : positive_cstr;
on_ctype_variance : (Variance.t list -> __ -> 'pcmp cstr_respects_variance) }

val on_ctype :
  checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
  Env.one_inductive_body -> Env.context -> Env.constructor_body -> Universe.t
  list -> ('a1, 'a2) on_constructor -> 'a2 on_type

val on_cargs :
  checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
  Env.one_inductive_body -> Env.context -> Env.constructor_body -> Universe.t
  list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx

val on_cindices :
  checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
  Env.one_inductive_body -> Env.context -> Env.constructor_body -> Universe.t
  list -> ('a1, 'a2) on_constructor -> 'a2 TemplateEnvTyping.ctx_inst

val on_ctype_positive :
  checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
  Env.one_inductive_body -> Env.context -> Env.constructor_body -> Universe.t
  list -> ('a1, 'a2) on_constructor -> positive_cstr

val on_ctype_variance :
  checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
  Env.one_inductive_body -> Env.context -> Env.constructor_body -> Universe.t
  list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
  cstr_respects_variance

type ('pcmp, 'p) on_constructors =
  (Env.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor) coq_All2

type on_projections =
  (Env.projection_body, __) coq_Alli
  (* singleton inductive, whose constructor was Build_on_projections *)

val on_projs :
  Env.mutual_inductive_body -> kername -> nat -> Env.one_inductive_body ->
  Env.context -> Env.constructor_body -> on_projections ->
  (Env.projection_body, __) coq_Alli

type constructor_univs = Universe.t list

val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

type 'p check_ind_sorts = __

type ('pcmp, 'p) on_ind_body = ('pcmp, 'p) TemplateGlobalMaps.on_ind_body = { 
onArity : 'p on_type; ind_cunivs : constructor_univs list;
onConstructors : ('pcmp, 'p) on_constructors; onProjections : __;
ind_sorts : 'p check_ind_sorts; onIndices : __ }

val onArity :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> nat -> Env.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type

val ind_cunivs :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> nat -> Env.one_inductive_body -> ('a1, 'a2) on_ind_body ->
  constructor_univs list

val onConstructors :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> nat -> Env.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
  on_constructors

val onProjections :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> nat -> Env.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

val ind_sorts :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> nat -> Env.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
  check_ind_sorts

val onIndices :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> nat -> Env.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

type on_variance = __

type ('pcmp, 'p) on_inductive = ('pcmp, 'p) TemplateGlobalMaps.on_inductive = { 
onInductives : (Env.one_inductive_body, ('pcmp, 'p) on_ind_body) coq_Alli;
onParams : 'p on_context; onVariance : on_variance }

val onInductives :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> ('a1, 'a2) on_inductive -> (Env.one_inductive_body, ('a1, 'a2)
  on_ind_body) coq_Alli

val onParams :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> ('a1, 'a2) on_inductive -> 'a2 on_context

val onVariance :
  checker_flags -> Env.global_env_ext -> kername -> Env.mutual_inductive_body
  -> ('a1, 'a2) on_inductive -> on_variance

type 'p on_constant_decl = __

type ('pcmp, 'p) on_global_decl = __

type ('pcmp, 'p) on_global_decls_data =
  ('pcmp, 'p) on_global_decl
  (* singleton inductive, whose constructor was Build_on_global_decls_data *)

val udecl :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
  on_global_decls_data -> universes_decl

val on_global_decl_d :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
  on_global_decls_data -> ('a1, 'a2) on_global_decl

type ('pcmp, 'p) on_global_decls = ('pcmp, 'p) TemplateGlobalMaps.on_global_decls =
| Coq_globenv_nil
| Coq_globenv_decl of Env.global_declarations * kername * Env.global_decl
   * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

val on_global_decls_rect :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
  (Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
  on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
  Env.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

val on_global_decls_rec :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
  (Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
  on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
  Env.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

val on_global_decls_sig_pack :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  Env.global_declarations -> ('a1, 'a2) on_global_decls ->
  Env.global_declarations * ('a1, 'a2) on_global_decls

val on_global_decls_Signature :
  checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
  Env.global_declarations -> (('a1, 'a2) on_global_decls,
  Env.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature

type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

val type_local_ctx_impl_gen :
  Env.global_env_ext -> Env.context -> Env.context -> Universe.t -> __ list
  -> (__, __ type_local_ctx) sigT -> (Env.context -> term -> Env.typ_or_sort
  -> (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
  type_local_ctx

val type_local_ctx_impl :
  Env.global_env_ext -> Env.context -> Env.context -> Universe.t -> 'a1
  type_local_ctx -> (Env.context -> term -> Env.typ_or_sort -> 'a1 -> 'a2) ->
  'a2 type_local_ctx

val sorts_local_ctx_impl_gen :
  Env.global_env_ext -> Env.context -> Env.context -> Universe.t list -> __
  list -> (__, __ sorts_local_ctx) sigT -> (Env.context -> term ->
  Env.typ_or_sort -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx)
  coq_All -> 'a1 sorts_local_ctx

val sorts_local_ctx_impl :
  Env.global_env_ext -> Env.context -> Env.context -> Universe.t list -> 'a1
  sorts_local_ctx -> (Env.context -> term -> Env.typ_or_sort -> 'a1 -> 'a2)
  -> 'a2 sorts_local_ctx

val cstr_respects_variance_impl_gen :
  Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
  Env.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT ->
  __ -> (__, __ cstr_respects_variance) coq_All -> 'a1 cstr_respects_variance

val cstr_respects_variance_impl :
  Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
  Env.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
  cstr_respects_variance

val on_constructor_impl_config_gen :
  Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
  Env.one_inductive_body -> Env.context -> Env.constructor_body -> Universe.t
  list -> ((checker_flags, __) prod, __) prod list -> checker_flags ->
  (((checker_flags, __) prod, __) prod, __) sigT -> (Env.context -> term ->
  Env.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
  'a2) -> (universes_decl -> Env.context -> term -> term -> conv_pb ->
  (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
  (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
  on_constructor

val on_constructors_impl_config_gen :
  Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
  Env.one_inductive_body -> Env.context -> Env.constructor_body list ->
  Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
  checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
  (((checker_flags, __) prod, __) prod, __) coq_All -> (Env.context -> term
  -> Env.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All ->
  'a2) -> (universes_decl -> Env.context -> term -> term -> conv_pb ->
  (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
  (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
  on_constructors

val ind_respects_variance_impl :
  Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
  Env.context -> __ -> 'a1 ind_respects_variance -> 'a2 ind_respects_variance

val on_variance_impl :
  Env.global_env -> universes_decl -> Variance.t list option -> checker_flags
  -> checker_flags -> on_variance -> on_variance

val on_global_env_impl_config :
  checker_flags -> checker_flags -> ((Env.global_env, universes_decl) prod ->
  Env.context -> term -> Env.typ_or_sort -> ('a1, 'a3) on_global_env -> ('a2,
  'a4) on_global_env -> 'a3 -> 'a4) -> ((Env.global_env, universes_decl) prod
  -> Env.context -> term -> term -> conv_pb -> ('a1, 'a3) on_global_env ->
  ('a2, 'a4) on_global_env -> 'a1 -> 'a2) -> Env.global_env -> ('a1, 'a3)
  on_global_env -> ('a2, 'a4) on_global_env

val on_global_env_impl :
  checker_flags -> ((Env.global_env, universes_decl) prod -> Env.context ->
  term -> Env.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
  on_global_env -> 'a2 -> 'a3) -> Env.global_env -> ('a1, 'a2) on_global_env
  -> ('a1, 'a3) on_global_env

module TemplateConversionPar :
 sig
  type cumul_gen = Coq__1.cumul_gen
 end

type coq_GuardChecker = { fix_guard : (Env.global_env_ext -> Env.context ->
                                      term mfixpoint -> bool);
                          cofix_guard : (Env.global_env_ext -> Env.context ->
                                        term mfixpoint -> bool) }

val fix_guard :
  coq_GuardChecker -> Env.global_env_ext -> Env.context -> term mfixpoint ->
  bool

val cofix_guard :
  coq_GuardChecker -> Env.global_env_ext -> Env.context -> term mfixpoint ->
  bool

val guard_checking : coq_GuardChecker

val destInd : term -> (inductive, Instance.t) prod option

val isFinite : recursivity_kind -> bool

val isCoFinite : recursivity_kind -> bool

val check_recursivity_kind :
  Env.global_env -> kername -> recursivity_kind -> bool

val check_one_fix : term def -> kername option

val wf_fixpoint : Env.global_env -> term def list -> bool

val check_one_cofix : term def -> kername option

val wf_cofixpoint : Env.global_env -> term def list -> bool

module Coq__2 : sig
 type typing =
 | Coq_type_Rel of nat * term context_decl
    * typing lift_typing coq_All_local_env
 | Coq_type_Sort of Universe.t * typing lift_typing coq_All_local_env
 | Coq_type_Cast of term * cast_kind * term * Universe.t * typing * typing
 | Coq_type_Prod of aname * term * term * Universe.t * Universe.t * typing
    * typing
 | Coq_type_Lambda of aname * term * term * Universe.t * term * typing
    * typing
 | Coq_type_LetIn of aname * term * term * term * Universe.t * term * 
    typing * typing * typing
 | Coq_type_App of term * term list * term * term * typing * typing_spine
 | Coq_type_Const of kername * Instance.t
    * typing lift_typing coq_All_local_env * Env.constant_body
 | Coq_type_Ind of inductive * Instance.t
    * typing lift_typing coq_All_local_env * Env.mutual_inductive_body
    * Env.one_inductive_body
 | Coq_type_Construct of inductive * nat * Instance.t
    * typing lift_typing coq_All_local_env * Env.mutual_inductive_body
    * Env.one_inductive_body * Env.constructor_body
 | Coq_type_Case of case_info * term predicate * term * term branch list
    * term list * Universe.t * Env.mutual_inductive_body
    * Env.one_inductive_body
    * (name binder_annot, term context_decl, __) coq_All2 * typing ctx_inst
    * typing * typing
    * (Env.constructor_body, term branch, (((name binder_annot, term
      context_decl, __) coq_All2, typing) prod, typing) prod) coq_All2i
 | Coq_type_Proj of projection * term * Instance.t
    * Env.mutual_inductive_body * Env.one_inductive_body
    * Env.constructor_body * Env.projection_body * term list * typing
 | Coq_type_Fix of term mfixpoint * nat * term def
    * typing lift_typing coq_All_local_env
    * (term def, (Universe.t, typing) sigT) coq_All
    * (term def, typing) coq_All
 | Coq_type_CoFix of term mfixpoint * nat * term def
    * typing lift_typing coq_All_local_env
    * (term def, (Universe.t, typing) sigT) coq_All
    * (term def, typing) coq_All
 | Coq_type_Int of int * kername * Env.constant_body
    * typing lift_typing coq_All_local_env * Env.primitive_invariants
 | Coq_type_Float of float * kername * Env.constant_body
    * typing lift_typing coq_All_local_env * Env.primitive_invariants
 | Coq_type_Conv of term * term * term * Universe.t * typing * typing
    * cumul_gen
 and typing_spine =
 | Coq_type_spine_nil of term
 | Coq_type_spine_cons of term * term list * aname * term * term * Universe.t
    * term * term * typing * cumul_gen * typing * typing_spine
end
include module type of struct include Coq__2 end

val typing_rect :
  checker_flags -> Env.global_env_ext -> (Env.context -> nat -> term
  context_decl -> typing lift_typing coq_All_local_env -> __ -> 'a1) ->
  (Env.context -> Universe.t -> typing lift_typing coq_All_local_env -> __ ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> Universe.t -> typing
  -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term ->
  Universe.t -> Universe.t -> typing -> 'a1 -> typing -> 'a1 -> 'a1) ->
  (Env.context -> aname -> term -> term -> Universe.t -> term -> typing ->
  'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term ->
  term -> Universe.t -> term -> typing -> 'a1 -> typing -> 'a1 -> typing ->
  'a1 -> 'a1) -> (Env.context -> term -> term list -> term -> term -> typing
  -> 'a1 -> __ -> __ -> typing_spine -> 'a1) -> (Env.context -> kername ->
  Instance.t -> typing lift_typing coq_All_local_env -> Env.constant_body ->
  __ -> __ -> 'a1) -> (Env.context -> inductive -> Instance.t -> typing
  lift_typing coq_All_local_env -> Env.mutual_inductive_body ->
  Env.one_inductive_body -> __ -> __ -> 'a1) -> (Env.context -> inductive ->
  nat -> Instance.t -> typing lift_typing coq_All_local_env ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> Env.constructor_body
  -> __ -> __ -> 'a1) -> (Env.context -> case_info -> term predicate -> term
  -> term branch list -> term list -> Universe.t -> Env.mutual_inductive_body
  -> Env.one_inductive_body -> __ -> __ -> (name binder_annot, term
  context_decl, __) coq_All2 -> __ -> __ -> typing ctx_inst -> typing -> 'a1
  -> __ -> typing -> 'a1 -> __ -> (Env.constructor_body, term branch, (((name
  binder_annot, term context_decl, __) coq_All2, typing) prod, typing) prod)
  coq_All2i -> 'a1) -> (Env.context -> projection -> term -> Instance.t ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> Env.constructor_body
  -> Env.projection_body -> __ -> term list -> typing -> 'a1 -> __ -> 'a1) ->
  (Env.context -> term mfixpoint -> nat -> term def -> __ -> __ -> typing
  lift_typing coq_All_local_env -> (term def, (Universe.t, typing) sigT)
  coq_All -> (term def, typing) coq_All -> __ -> 'a1) -> (Env.context -> term
  mfixpoint -> nat -> term def -> __ -> __ -> typing lift_typing
  coq_All_local_env -> (term def, (Universe.t, typing) sigT) coq_All -> (term
  def, typing) coq_All -> __ -> 'a1) -> (Env.context -> int -> kername ->
  Env.constant_body -> typing lift_typing coq_All_local_env -> __ -> __ ->
  Env.primitive_invariants -> 'a1) -> (Env.context -> float -> kername ->
  Env.constant_body -> typing lift_typing coq_All_local_env -> __ -> __ ->
  Env.primitive_invariants -> 'a1) -> (Env.context -> term -> term -> term ->
  Universe.t -> typing -> 'a1 -> typing -> 'a1 -> cumul_gen -> 'a1) ->
  Env.context -> term -> term -> typing -> 'a1

val typing_rec :
  checker_flags -> Env.global_env_ext -> (Env.context -> nat -> term
  context_decl -> typing lift_typing coq_All_local_env -> __ -> 'a1) ->
  (Env.context -> Universe.t -> typing lift_typing coq_All_local_env -> __ ->
  'a1) -> (Env.context -> term -> cast_kind -> term -> Universe.t -> typing
  -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term ->
  Universe.t -> Universe.t -> typing -> 'a1 -> typing -> 'a1 -> 'a1) ->
  (Env.context -> aname -> term -> term -> Universe.t -> term -> typing ->
  'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term ->
  term -> Universe.t -> term -> typing -> 'a1 -> typing -> 'a1 -> typing ->
  'a1 -> 'a1) -> (Env.context -> term -> term list -> term -> term -> typing
  -> 'a1 -> __ -> __ -> typing_spine -> 'a1) -> (Env.context -> kername ->
  Instance.t -> typing lift_typing coq_All_local_env -> Env.constant_body ->
  __ -> __ -> 'a1) -> (Env.context -> inductive -> Instance.t -> typing
  lift_typing coq_All_local_env -> Env.mutual_inductive_body ->
  Env.one_inductive_body -> __ -> __ -> 'a1) -> (Env.context -> inductive ->
  nat -> Instance.t -> typing lift_typing coq_All_local_env ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> Env.constructor_body
  -> __ -> __ -> 'a1) -> (Env.context -> case_info -> term predicate -> term
  -> term branch list -> term list -> Universe.t -> Env.mutual_inductive_body
  -> Env.one_inductive_body -> __ -> __ -> (name binder_annot, term
  context_decl, __) coq_All2 -> __ -> __ -> typing ctx_inst -> typing -> 'a1
  -> __ -> typing -> 'a1 -> __ -> (Env.constructor_body, term branch, (((name
  binder_annot, term context_decl, __) coq_All2, typing) prod, typing) prod)
  coq_All2i -> 'a1) -> (Env.context -> projection -> term -> Instance.t ->
  Env.mutual_inductive_body -> Env.one_inductive_body -> Env.constructor_body
  -> Env.projection_body -> __ -> term list -> typing -> 'a1 -> __ -> 'a1) ->
  (Env.context -> term mfixpoint -> nat -> term def -> __ -> __ -> typing
  lift_typing coq_All_local_env -> (term def, (Universe.t, typing) sigT)
  coq_All -> (term def, typing) coq_All -> __ -> 'a1) -> (Env.context -> term
  mfixpoint -> nat -> term def -> __ -> __ -> typing lift_typing
  coq_All_local_env -> (term def, (Universe.t, typing) sigT) coq_All -> (term
  def, typing) coq_All -> __ -> 'a1) -> (Env.context -> int -> kername ->
  Env.constant_body -> typing lift_typing coq_All_local_env -> __ -> __ ->
  Env.primitive_invariants -> 'a1) -> (Env.context -> float -> kername ->
  Env.constant_body -> typing lift_typing coq_All_local_env -> __ -> __ ->
  Env.primitive_invariants -> 'a1) -> (Env.context -> term -> term -> term ->
  Universe.t -> typing -> 'a1 -> typing -> 'a1 -> cumul_gen -> 'a1) ->
  Env.context -> term -> term -> typing -> 'a1

val typing_spine_rect :
  checker_flags -> Env.global_env_ext -> (Env.context -> term -> 'a1) ->
  (Env.context -> term -> term list -> aname -> term -> term -> Universe.t ->
  term -> term -> typing -> cumul_gen -> typing -> typing_spine -> 'a1 ->
  'a1) -> Env.context -> term -> term list -> term -> typing_spine -> 'a1

val typing_spine_rec :
  checker_flags -> Env.global_env_ext -> (Env.context -> term -> 'a1) ->
  (Env.context -> term -> term list -> aname -> term -> term -> Universe.t ->
  term -> term -> typing -> cumul_gen -> typing -> typing_spine -> 'a1 ->
  'a1) -> Env.context -> term -> term list -> term -> typing_spine -> 'a1

type typing_sig = typing

val typing_sig_pack :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
  typing -> (Env.context * (term * term)) * typing

val typing_Signature :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
  (typing, Env.context * (term * term), typing_sig) coq_Signature

type typing_spine_sig = typing_spine

val typing_spine_sig_pack :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> term list ->
  term -> typing_spine -> (Env.context * (term * (term
  list * term))) * typing_spine

val typing_spine_Signature :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> term list ->
  term -> (typing_spine, Env.context * (term * (term list * term)),
  typing_spine_sig) coq_Signature

type 'p unlift_opt_pred = 'p

module Coq__3 : sig
 type infer_sorting = (Universe.t, typing) sigT
end
include module type of struct include Coq__3 end

module TemplateTyping :
 sig
  type typing = Coq__2.typing

  type infer_sorting = Coq__3.infer_sorting
 end

module TemplateDeclarationTyping :
 sig
  type isType = typing TemplateEnvTyping.infer_sort

  type 'p coq_Forall_decls_typing =
    (cumul_gen, 'p TemplateEnvTyping.lift_typing)
    TemplateGlobalMaps.on_global_env

  type type_local_decl = __

  val refine_type :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
    term -> typing -> typing

  type wf_local_rel =
    typing TemplateEnvTyping.lift_typing TemplateEnvTyping.coq_All_local_rel

  val on_wf_global_env_impl_config :
    checker_flags -> checker_flags -> checker_flags -> Env.global_env ->
    (cumul_gen, typing TemplateEnvTyping.lift_typing)
    TemplateGlobalMaps.on_global_env -> (Env.global_env_ext -> Env.context ->
    conv_pb -> term -> term -> cumul_gen -> cumul_gen) -> ((Env.global_env,
    universes_decl) prod -> Env.context -> term -> Env.typ_or_sort ->
    (cumul_gen, typing TemplateEnvTyping.lift_typing)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a1)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
    TemplateGlobalMaps.on_global_env -> 'a1 -> 'a2) -> (cumul_gen, 'a1)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
    TemplateGlobalMaps.on_global_env

  val on_wf_global_env_impl :
    checker_flags -> Env.global_env -> (cumul_gen, typing
    TemplateEnvTyping.lift_typing) TemplateGlobalMaps.on_global_env ->
    ((Env.global_env, universes_decl) prod -> Env.context -> term ->
    Env.typ_or_sort -> (cumul_gen, typing TemplateEnvTyping.lift_typing)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a1)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
    TemplateGlobalMaps.on_global_env -> 'a1 -> 'a2) -> (cumul_gen, 'a1)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
    TemplateGlobalMaps.on_global_env
 end

type isType = typing TemplateEnvTyping.infer_sort

type 'p coq_Forall_decls_typing =
  (cumul_gen, 'p TemplateEnvTyping.lift_typing)
  TemplateGlobalMaps.on_global_env

type type_local_decl = __

val refine_type :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> term -> term
  -> typing -> typing

type wf_local_rel =
  typing TemplateEnvTyping.lift_typing TemplateEnvTyping.coq_All_local_rel

val on_wf_global_env_impl_config :
  checker_flags -> checker_flags -> checker_flags -> Env.global_env ->
  (cumul_gen, typing TemplateEnvTyping.lift_typing)
  TemplateGlobalMaps.on_global_env -> (Env.global_env_ext -> Env.context ->
  conv_pb -> term -> term -> cumul_gen -> cumul_gen) -> ((Env.global_env,
  universes_decl) prod -> Env.context -> term -> Env.typ_or_sort ->
  (cumul_gen, typing TemplateEnvTyping.lift_typing)
  TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a1)
  TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
  TemplateGlobalMaps.on_global_env -> 'a1 -> 'a2) -> (cumul_gen, 'a1)
  TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
  TemplateGlobalMaps.on_global_env

val on_wf_global_env_impl :
  checker_flags -> Env.global_env -> (cumul_gen, typing
  TemplateEnvTyping.lift_typing) TemplateGlobalMaps.on_global_env ->
  ((Env.global_env, universes_decl) prod -> Env.context -> term ->
  Env.typ_or_sort -> (cumul_gen, typing TemplateEnvTyping.lift_typing)
  TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a1)
  TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
  TemplateGlobalMaps.on_global_env -> 'a1 -> 'a2) -> (cumul_gen, 'a1)
  TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
  TemplateGlobalMaps.on_global_env

val typing_spine_size :
  checker_flags -> (Env.global_env_ext -> Env.context -> term -> term ->
  typing -> size) -> Env.global_env_ext -> Env.context -> term -> term list
  -> term -> typing_spine -> size

val ctx_inst_size :
  (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
  Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
  ctx_inst -> size

val typing_size :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
  typing -> size

val globdecls_size : Env.global_declarations -> size

val globenv_size : Env.global_env -> size

type wf = (cumul_gen, typing lift_typing) on_global_env

type wf_ext = (cumul_gen, typing lift_typing) on_global_env_ext

val typing_wf_local :
  checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
  typing -> typing lift_typing coq_All_local_env

val type_Prop : checker_flags -> Env.global_env_ext -> typing

val type_Prop_wf :
  checker_flags -> Env.global_env_ext -> Env.context -> typing lift_typing
  coq_All_local_env -> typing

type ('p, 'x) env_prop =
  Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> term -> term -> typing -> ((cumul_gen, 'p lift_typing)
  on_global_env, ('x, 'p) prod) prod

val env_prop_typing :
  checker_flags -> ('a1, 'a2) env_prop -> Env.global_env_ext -> wf ->
  Env.context -> typing lift_typing coq_All_local_env -> term -> term ->
  typing -> 'a1

val env_prop_wf_local :
  checker_flags -> ('a1, 'a2) env_prop -> Env.global_env_ext -> wf ->
  Env.context -> typing lift_typing coq_All_local_env -> 'a2

val env_prop_sigma :
  checker_flags -> ('a1, 'a2) env_prop -> Env.global_env -> wf -> (cumul_gen,
  'a1 lift_typing) on_global_env

val wf_local_app_l :
  checker_flags -> Env.global_env_ext -> Env.context -> Env.context -> typing
  lift_typing coq_All_local_env -> typing lift_typing coq_All_local_env

val wf_local_inv :
  checker_flags -> Env.global_env_ext -> Env.context -> typing lift_typing
  coq_All_local_env -> term context_decl -> term context_decl list -> (typing
  lift_typing coq_All_local_env, __) sigT

type 'p coq_Forall_typing_spine =
| Forall_type_spine_nil of term
| Forall_type_spine_cons of term * term list * aname * term * term
   * Universe.t * term * term * typing_spine * typing * cumul_gen * typing
   * 'p * 'p * 'p coq_Forall_typing_spine

val coq_Forall_typing_spine_rect :
  checker_flags -> Env.global_env_ext -> Env.context -> (term -> 'a2) ->
  (term -> term list -> aname -> term -> term -> Universe.t -> term -> term
  -> typing_spine -> typing -> cumul_gen -> typing -> 'a1 -> 'a1 -> 'a1
  coq_Forall_typing_spine -> 'a2 -> 'a2) -> term -> term list -> term ->
  typing_spine -> 'a1 coq_Forall_typing_spine -> 'a2

val coq_Forall_typing_spine_rec :
  checker_flags -> Env.global_env_ext -> Env.context -> (term -> 'a2) ->
  (term -> term list -> aname -> term -> term -> Universe.t -> term -> term
  -> typing_spine -> typing -> cumul_gen -> typing -> 'a1 -> 'a1 -> 'a1
  coq_Forall_typing_spine -> 'a2 -> 'a2) -> term -> term list -> term ->
  typing_spine -> 'a1 coq_Forall_typing_spine -> 'a2

val typing_ind_env :
  checker_flags -> (Env.global_env_ext -> wf -> Env.context -> typing
  lift_typing coq_All_local_env -> (typing, 'a1) coq_All_local_env_over ->
  'a2) -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> nat -> term context_decl -> __ -> 'a2 -> 'a1) ->
  (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> Universe.t -> 'a2 -> __ -> 'a1) -> (Env.global_env_ext
  -> wf -> Env.context -> typing lift_typing coq_All_local_env -> term ->
  cast_kind -> term -> Universe.t -> typing -> 'a1 -> typing -> 'a1 -> 'a1)
  -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> aname -> term -> term -> Universe.t -> Universe.t ->
  'a2 -> typing -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.global_env_ext -> wf
  -> Env.context -> typing lift_typing coq_All_local_env -> aname -> term ->
  term -> Universe.t -> term -> 'a2 -> typing -> 'a1 -> typing -> 'a1 -> 'a1)
  -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> aname -> term -> term -> term -> Universe.t -> term ->
  'a2 -> typing -> 'a1 -> typing -> 'a1 -> typing -> 'a1 -> 'a1) ->
  (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> term -> term list -> term -> term -> typing -> 'a1 ->
  __ -> __ -> typing_spine -> 'a1 coq_Forall_typing_spine -> 'a1) ->
  (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> kername -> Instance.t -> Env.constant_body ->
  (cumul_gen, 'a1 lift_typing) on_global_env -> 'a2 -> __ -> __ -> 'a1) ->
  (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> inductive -> Instance.t -> Env.mutual_inductive_body
  -> Env.one_inductive_body -> __ -> (cumul_gen, 'a1 lift_typing)
  on_global_env -> 'a2 -> __ -> 'a1) -> (Env.global_env_ext -> wf ->
  Env.context -> typing lift_typing coq_All_local_env -> inductive -> nat ->
  Instance.t -> Env.mutual_inductive_body -> Env.one_inductive_body ->
  Env.constructor_body -> __ -> (cumul_gen, 'a1 lift_typing) on_global_env ->
  'a2 -> __ -> 'a1) -> (Env.global_env_ext -> wf -> Env.context -> typing
  lift_typing coq_All_local_env -> case_info -> term predicate -> term ->
  term branch list -> term list -> Universe.t -> Env.mutual_inductive_body ->
  Env.one_inductive_body -> __ -> (cumul_gen, 'a1 lift_typing) on_global_env
  -> 'a2 -> __ -> (name binder_annot, term context_decl, __) coq_All2 -> __
  -> __ -> (typing, 'a1) prod ctx_inst -> typing -> 'a1 -> 'a2 -> __ ->
  typing -> 'a1 -> __ -> (Env.constructor_body, term branch, (((name
  binder_annot, term context_decl, __) coq_All2, (typing, 'a1) prod) prod,
  (typing, 'a1) prod) prod) coq_All2i -> 'a1) -> (Env.global_env_ext -> wf ->
  Env.context -> typing lift_typing coq_All_local_env -> projection -> term
  -> Instance.t -> Env.mutual_inductive_body -> Env.one_inductive_body ->
  Env.constructor_body -> Env.projection_body -> __ -> term list ->
  (cumul_gen, 'a1 lift_typing) on_global_env -> 'a2 -> typing -> 'a1 -> __ ->
  'a1) -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> term def list -> nat -> term def -> __ -> __ -> 'a2 ->
  (term def, (typing, 'a1) lift_typing2 on_def_type) coq_All -> (term def,
  (typing, 'a1) lift_typing2 on_def_body) coq_All -> __ -> 'a1) ->
  (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> term def list -> nat -> term def -> __ -> __ -> 'a2 ->
  (term def, (typing, 'a1) lift_typing2 on_def_type) coq_All -> (term def,
  (typing, 'a1) lift_typing2 on_def_body) coq_All -> __ -> 'a1) ->
  (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> int -> kername -> Env.constant_body -> 'a2 -> __ -> __
  -> Env.primitive_invariants -> 'a1) -> (Env.global_env_ext -> wf ->
  Env.context -> typing lift_typing coq_All_local_env -> float -> kername ->
  Env.constant_body -> 'a2 -> __ -> __ -> Env.primitive_invariants -> 'a1) ->
  (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> term -> term -> term -> Universe.t -> 'a2 -> typing ->
  'a1 -> typing -> 'a1 -> cumul_gen -> 'a1) -> ('a1, 'a2) env_prop

val nth_error_All_local_env :
  term context_decl list -> nat -> 'a1 coq_All_local_env -> (term
  context_decl, 'a1 on_local_decl) on_some

val lookup_on_global_env :
  checker_flags -> Env.global_env -> kername -> Env.global_decl -> ('a1, 'a2)
  on_global_env -> (Env.global_env_ext, (('a1, 'a2) on_global_env,
  (Env.strictly_extends_decls, ('a1, 'a2) on_global_decl) prod) prod) sigT

val coq_All_local_env_app_inv :
  Env.context -> Env.context -> 'a1 coq_All_local_env -> ('a1
  coq_All_local_env, 'a1 coq_All_local_env) prod

val coq_All_local_env_lookup :
  Env.context -> nat -> term context_decl -> 'a1 coq_All_local_env -> 'a1
  on_local_decl

val coq_All_local_env_app :
  checker_flags -> Env.context -> Env.context -> ('a1 coq_All_local_env, 'a1
  coq_All_local_env) prod -> 'a1 coq_All_local_env

val coq_All_local_env_map :
  checker_flags -> (term -> term) -> Env.context -> 'a1 coq_All_local_env ->
  'a1 coq_All_local_env

val lookup_wf_local :
  Env.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env

val lookup_wf_local_decl :
  Env.context -> 'a1 coq_All_local_env -> nat -> term context_decl -> ('a1
  coq_All_local_env, 'a1 on_local_decl) sigT

type 'p on_wf_local_decl = __

val nth_error_All_local_env_over :
  checker_flags -> Env.global_env_ext -> term context_decl list -> nat ->
  term context_decl -> typing lift_typing coq_All_local_env -> (typing, 'a1)
  coq_All_local_env_over -> ((typing, 'a1) coq_All_local_env_over, 'a1
  on_wf_local_decl) prod

val wf_ext_wf : checker_flags -> Env.global_env_ext -> wf_ext -> wf
