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
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Lookup =
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
 struct
  (** val lookup_constant_gen :
      (kername -> E.global_decl option) -> kername -> E.constant_body option **)

  let lookup_constant_gen lookup kn =
    match lookup kn with
    | Some g ->
      (match g with
       | E.ConstantDecl d -> Some d
       | E.InductiveDecl _ -> None)
    | None -> None

  (** val lookup_constant :
      E.global_env -> kername -> E.constant_body option **)

  let lookup_constant _UU03a3_ =
    lookup_constant_gen (E.lookup_env _UU03a3_)

  (** val lookup_minductive_gen :
      (kername -> E.global_decl option) -> kername -> E.mutual_inductive_body
      option **)

  let lookup_minductive_gen lookup mind =
    match lookup mind with
    | Some g ->
      (match g with
       | E.ConstantDecl _ -> None
       | E.InductiveDecl decl -> Some decl)
    | None -> None

  (** val lookup_minductive :
      E.global_env -> kername -> E.mutual_inductive_body option **)

  let lookup_minductive _UU03a3_ =
    lookup_minductive_gen (E.lookup_env _UU03a3_)

  (** val lookup_inductive_gen :
      (kername -> E.global_decl option) -> inductive ->
      (E.mutual_inductive_body, E.one_inductive_body) prod option **)

  let lookup_inductive_gen lookup ind =
    match lookup_minductive_gen lookup ind.inductive_mind with
    | Some mdecl ->
      (match nth_error (E.ind_bodies mdecl) ind.inductive_ind with
       | Some idecl -> Some (Coq_pair (mdecl, idecl))
       | None -> None)
    | None -> None

  (** val lookup_inductive :
      E.global_env -> inductive -> (E.mutual_inductive_body,
      E.one_inductive_body) prod option **)

  let lookup_inductive _UU03a3_ =
    lookup_inductive_gen (E.lookup_env _UU03a3_)

  (** val lookup_constructor_gen :
      (kername -> E.global_decl option) -> inductive -> nat ->
      ((E.mutual_inductive_body, E.one_inductive_body) prod,
      E.constructor_body) prod option **)

  let lookup_constructor_gen lookup ind k =
    match lookup_inductive_gen lookup ind with
    | Some p ->
      let Coq_pair (mdecl, idecl) = p in
      (match nth_error (E.ind_ctors idecl) k with
       | Some cdecl -> Some (Coq_pair ((Coq_pair (mdecl, idecl)), cdecl))
       | None -> None)
    | None -> None

  (** val lookup_constructor :
      E.global_env -> inductive -> nat -> ((E.mutual_inductive_body,
      E.one_inductive_body) prod, E.constructor_body) prod option **)

  let lookup_constructor _UU03a3_ =
    lookup_constructor_gen (E.lookup_env _UU03a3_)

  (** val lookup_projection_gen :
      (kername -> E.global_decl option) -> projection ->
      (((E.mutual_inductive_body, E.one_inductive_body) prod,
      E.constructor_body) prod, E.projection_body) prod option **)

  let lookup_projection_gen lookup p =
    match lookup_constructor_gen lookup p.proj_ind O with
    | Some p0 ->
      let Coq_pair (p1, cdecl) = p0 in
      let Coq_pair (mdecl, idecl) = p1 in
      (match nth_error (E.ind_projs idecl) p.proj_arg with
       | Some pdecl ->
         Some (Coq_pair ((Coq_pair ((Coq_pair (mdecl, idecl)), cdecl)),
           pdecl))
       | None -> None)
    | None -> None

  (** val lookup_projection :
      E.global_env -> projection -> (((E.mutual_inductive_body,
      E.one_inductive_body) prod, E.constructor_body) prod,
      E.projection_body) prod option **)

  let lookup_projection _UU03a3_ =
    lookup_projection_gen (E.lookup_env _UU03a3_)

  (** val on_udecl_decl : (universes_decl -> 'a1) -> E.global_decl -> 'a1 **)

  let on_udecl_decl f = function
  | E.ConstantDecl cb -> f (E.cst_universes cb)
  | E.InductiveDecl mb -> f (E.ind_universes mb)

  (** val universes_decl_of_decl : E.global_decl -> universes_decl **)

  let universes_decl_of_decl =
    on_udecl_decl (fun x -> x)

  (** val global_levels : ContextSet.t -> LevelSet.t **)

  let global_levels univs =
    LevelSet.union (ContextSet.levels univs)
      (LevelSet.singleton Level.Coq_lzero)

  (** val global_constraints : E.global_env -> ConstraintSet.t **)

  let global_constraints _UU03a3_ =
    snd (E.universes _UU03a3_)

  (** val global_uctx : E.global_env -> ContextSet.t **)

  let global_uctx _UU03a3_ =
    Coq_pair ((global_levels (E.universes _UU03a3_)),
      (global_constraints _UU03a3_))

  (** val global_ext_levels : E.global_env_ext -> LevelSet.t **)

  let global_ext_levels _UU03a3_ =
    LevelSet.union (levels_of_udecl (snd _UU03a3_))
      (global_levels (E.universes (fst _UU03a3_)))

  (** val global_ext_constraints : E.global_env_ext -> ConstraintSet.t **)

  let global_ext_constraints _UU03a3_ =
    ConstraintSet.union (constraints_of_udecl (snd _UU03a3_))
      (global_constraints (fst _UU03a3_))

  (** val global_ext_uctx : E.global_env_ext -> ContextSet.t **)

  let global_ext_uctx _UU03a3_ =
    Coq_pair ((global_ext_levels _UU03a3_), (global_ext_constraints _UU03a3_))

  (** val wf_universe_dec : E.global_env_ext -> Universe.t -> sumbool **)

  let wf_universe_dec _UU03a3_ = function
  | Universe.Coq_lType t0 ->
    let rec f = function
    | Coq_nil -> Coq_left
    | Coq_cons (y, l0) ->
      (match f l0 with
       | Coq_left ->
         LevelSetProp.coq_In_dec (LevelExpr.get_level y)
           (global_ext_levels _UU03a3_)
       | Coq_right -> Coq_right)
    in f t0
  | _ -> Coq_left

  (** val declared_ind_declared_constructors :
      checker_flags -> E.global_env -> inductive -> E.mutual_inductive_body
      -> E.one_inductive_body -> (E.constructor_body, __) coq_Alli **)

  let declared_ind_declared_constructors _ _ _ _ oib =
    forall_nth_error_Alli O (E.ind_ctors oib) (Obj.magic __)
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

module EnvTyping =
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
 struct
  type 'typing coq_All_local_env =
  | Coq_localenv_nil
  | Coq_localenv_cons_abs of E.context * aname * T.term
     * 'typing coq_All_local_env * 'typing
  | Coq_localenv_cons_def of E.context * aname * T.term * T.term
     * 'typing coq_All_local_env * 'typing * 'typing

  (** val coq_All_local_env_rect :
      'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
      'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
      coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
      coq_All_local_env -> 'a2 **)

  let rec coq_All_local_env_rect f f0 f1 _ = function
  | Coq_localenv_nil -> f
  | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
    f0 _UU0393_ na t0 a0 (coq_All_local_env_rect f f0 f1 _UU0393_ a0) t1
  | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2) ->
    f1 _UU0393_ na b t0 a0 (coq_All_local_env_rect f f0 f1 _UU0393_ a0) t1 t2

  (** val coq_All_local_env_rec :
      'a2 -> (E.context -> aname -> T.term -> 'a1 coq_All_local_env -> 'a2 ->
      'a1 -> 'a2) -> (E.context -> aname -> T.term -> T.term -> 'a1
      coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> E.context -> 'a1
      coq_All_local_env -> 'a2 **)

  let rec coq_All_local_env_rec f f0 f1 _ = function
  | Coq_localenv_nil -> f
  | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
    f0 _UU0393_ na t0 a0 (coq_All_local_env_rec f f0 f1 _UU0393_ a0) t1
  | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2) ->
    f1 _UU0393_ na b t0 a0 (coq_All_local_env_rec f f0 f1 _UU0393_ a0) t1 t2

  type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

  (** val coq_All_local_env_sig_pack :
      E.context -> 'a1 coq_All_local_env -> E.context * 'a1 coq_All_local_env **)

  let coq_All_local_env_sig_pack x all_local_env_var =
    x,all_local_env_var

  (** val coq_All_local_env_Signature :
      E.context -> ('a1 coq_All_local_env, E.context, 'a1
      coq_All_local_env_sig) coq_Signature **)

  let coq_All_local_env_Signature =
    coq_All_local_env_sig_pack

  (** val coq_NoConfusionPackage_All_local_env :
      (E.context * 'a1 coq_All_local_env) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_All_local_env =
    Build_NoConfusionPackage

  (** val coq_All_local_env_fold :
      (nat -> T.term -> T.term) -> E.context -> ('a1 coq_All_local_env, 'a1
      coq_All_local_env) iffT **)

  let coq_All_local_env_fold f _UU0393_ =
    Coq_pair ((fun x ->
      let rec f0 _ = function
      | Coq_localenv_nil -> Coq_localenv_nil
      | Coq_localenv_cons_abs (_UU0393_0, na, t0, a0, t1) ->
        Coq_localenv_cons_abs ((fold_context_k f _UU0393_0),
          (E.vass na t0).decl_name,
          (f (length _UU0393_0) (E.vass na t0).decl_type), (f0 _UU0393_0 a0),
          t1)
      | Coq_localenv_cons_def (_UU0393_0, na, b, t0, a0, t1, t2) ->
        Coq_localenv_cons_def ((fold_context_k f _UU0393_0),
          (E.vdef na b t0).decl_name, (f (length _UU0393_0) b),
          (f (length _UU0393_0) (E.vdef na b t0).decl_type),
          (f0 _UU0393_0 a0), t1, t2)
      in f0 _UU0393_ x),
      (let rec f0 l h =
         match l with
         | Coq_nil -> Coq_localenv_nil
         | Coq_cons (y, l0) ->
           let { decl_name = decl_name0; decl_body = decl_body0; decl_type =
             decl_type0 } = y
           in
           (match decl_body0 with
            | Some t0 ->
              let h0 =
                (snoc (fold_context_k f l0)
                  (map_decl (f (length l0)) { decl_name = decl_name0;
                    decl_body = (Some t0); decl_type = decl_type0 })),h
              in
              let h2 = let _,pr2 = h0 in pr2 in
              (match h2 with
               | Coq_localenv_cons_def (_, _, _, _, a, p, p0) ->
                 let iH_UU0393_ = f0 l0 a in
                 Coq_localenv_cons_def (l0, decl_name0, t0, decl_type0,
                 iH_UU0393_, p, p0)
               | _ -> assert false (* absurd case *))
            | None ->
              let h0 =
                (snoc (fold_context_k f l0)
                  (map_decl (f (length l0)) { decl_name = decl_name0;
                    decl_body = None; decl_type = decl_type0 })),h
              in
              let h2 = let _,pr2 = h0 in pr2 in
              (match h2 with
               | Coq_localenv_cons_abs (_, _, _, a, p) ->
                 let iH_UU0393_ = f0 l0 a in
                 Coq_localenv_cons_abs (l0, decl_name0, decl_type0,
                 iH_UU0393_, p)
               | _ -> assert false (* absurd case *)))
       in f0 _UU0393_))

  (** val coq_All_local_env_impl :
      E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
      E.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env **)

  let rec coq_All_local_env_impl _ a x =
    match a with
    | Coq_localenv_nil -> Coq_localenv_nil
    | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
      Coq_localenv_cons_abs (_UU0393_, na, t0,
        (coq_All_local_env_impl _UU0393_ a0 x), (x _UU0393_ t0 Sort t1))
    | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2) ->
      Coq_localenv_cons_def (_UU0393_, na, b, t0,
        (coq_All_local_env_impl _UU0393_ a0 x), (x _UU0393_ t0 Sort t1),
        (x _UU0393_ b (Typ t0) t2))

  (** val coq_All_local_env_impl_ind :
      E.context -> 'a1 coq_All_local_env -> (E.context -> T.term ->
      E.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
      coq_All_local_env **)

  let rec coq_All_local_env_impl_ind _ = function
  | Coq_localenv_nil -> (fun _ -> Coq_localenv_nil)
  | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
    let iHX = coq_All_local_env_impl_ind _UU0393_ a0 in
    (fun x -> Coq_localenv_cons_abs (_UU0393_, na, t0, (iHX x),
    (x _UU0393_ t0 Sort (iHX x) t1)))
  | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2) ->
    let iHX = coq_All_local_env_impl_ind _UU0393_ a0 in
    (fun x -> Coq_localenv_cons_def (_UU0393_, na, b, t0, (iHX x),
    (x _UU0393_ t0 Sort (iHX x) t1), (x _UU0393_ b (Typ t0) (iHX x) t2)))

  (** val coq_All_local_env_skipn :
      E.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env **)

  let rec coq_All_local_env_skipn _ a n =
    match a with
    | Coq_localenv_nil -> Coq_localenv_nil
    | Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
      (match n with
       | O -> Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1)
       | S n0 -> coq_All_local_env_skipn _UU0393_ a0 n0)
    | Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2) ->
      (match n with
       | O -> Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2)
       | S n0 -> coq_All_local_env_skipn _UU0393_ a0 n0)

  type 'p coq_All_local_rel = 'p coq_All_local_env

  (** val coq_All_local_rel_nil : E.context -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_nil _ =
    Coq_localenv_nil

  (** val coq_All_local_rel_abs :
      E.context -> E.context -> T.term -> aname -> 'a1 coq_All_local_rel ->
      'a1 -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_abs _ _UU0393_' a na x x0 =
    Coq_localenv_cons_abs (_UU0393_', na, a, x, x0)

  (** val coq_All_local_rel_def :
      E.context -> E.context -> T.term -> T.term -> aname -> 'a1
      coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_def _ _UU0393_' t0 a na x x0 x1 =
    Coq_localenv_cons_def (_UU0393_', na, t0, a, x, x0, x1)

  (** val coq_All_local_rel_local :
      E.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel **)

  let coq_All_local_rel_local _UU0393_ h =
    coq_All_local_env_impl _UU0393_ h (fun _ _ _ h' -> h')

  (** val coq_All_local_local_rel :
      E.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env **)

  let coq_All_local_local_rel _UU0393_ x =
    coq_All_local_env_impl _UU0393_ x (fun _ _ _ xX -> xX)

  (** val coq_All_local_app_rel :
      E.context -> E.context -> 'a1 coq_All_local_env -> ('a1
      coq_All_local_env, 'a1 coq_All_local_rel) prod **)

  let rec coq_All_local_app_rel _UU0393_ _UU0393_' h_UU0393_ =
    match _UU0393_' with
    | Coq_nil -> Coq_pair (h_UU0393_, Coq_localenv_nil)
    | Coq_cons (_, l) ->
      (match h_UU0393_ with
       | Coq_localenv_nil -> assert false (* absurd case *)
       | Coq_localenv_cons_abs (_, na, t0, x, x0) ->
         let p = coq_All_local_app_rel _UU0393_ l x in
         let Coq_pair (a, a0) = p in
         Coq_pair (a, (Coq_localenv_cons_abs (l, na, t0, a0, x0)))
       | Coq_localenv_cons_def (_, na, b, t0, x, x0, x1) ->
         let p = coq_All_local_app_rel _UU0393_ l x in
         let Coq_pair (a, a0) = p in
         Coq_pair (a, (Coq_localenv_cons_def (l, na, b, t0, a0, x0, x1))))

  (** val coq_All_local_rel_app :
      E.context -> E.context -> 'a1 coq_All_local_env -> 'a1
      coq_All_local_rel -> 'a1 coq_All_local_env **)

  let rec coq_All_local_rel_app _UU0393_ _ x = function
  | Coq_localenv_nil -> x
  | Coq_localenv_cons_abs (_UU0393_0, na, t0, a, t1) ->
    Coq_localenv_cons_abs ((app _UU0393_0 _UU0393_), na, t0,
      (coq_All_local_rel_app _UU0393_ _UU0393_0 x a), t1)
  | Coq_localenv_cons_def (_UU0393_0, na, b, t0, a, t1, t2) ->
    Coq_localenv_cons_def ((app _UU0393_0 _UU0393_), na, b, t0,
      (coq_All_local_rel_app _UU0393_ _UU0393_0 x a), t1, t2)

  type 'p on_local_decl = __

  type 'p on_def_type = 'p

  type 'p on_def_body = 'p

  type ('check, 'infer_sort) lift_judgment = __

  (** val lift_judgment_impl :
      E.global_env_ext -> E.global_env_ext -> E.context -> E.context ->
      T.term -> T.term -> E.typ_or_sort -> ('a1, 'a2) lift_judgment ->
      (T.term -> 'a1 -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment **)

  let lift_judgment_impl _ _ _ _ _ _ t0 hT hPQ hPsQs =
    match t0 with
    | Typ t1 -> Obj.magic hPQ t1 hT
    | Sort -> Obj.magic hPsQs hT

  type 'wf_term lift_wf_term =
    (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

  type 'sorting infer_sort = (Universe.t, 'sorting) sigT

  type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

  type ('checking, 'sorting) lift_sorting =
    ('checking, 'sorting infer_sort) lift_judgment

  type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

  (** val infer_sort_impl :
      E.global_env_ext -> E.global_env_ext -> E.context -> E.context ->
      T.term -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort ->
      ('a1 -> 'a2) -> 'a2 infer_sort **)

  let infer_sort_impl _ _ _ _ _ _ f = function
  | Coq_existT (x, p) ->
    let s = projT1 (Coq_existT (x, p)) in
    (fun hPQ -> Coq_existT ((f s), (hPQ p)))

  (** val infer_typing_sort_impl :
      E.global_env_ext -> E.global_env_ext -> E.context -> E.context ->
      T.term -> T.term -> (Universe.t -> Universe.t) -> 'a1 infer_sort ->
      ('a1 -> 'a2) -> 'a2 infer_sort **)

  let infer_typing_sort_impl =
    infer_sort_impl

  (** val lift_typing_impl :
      E.global_env_ext -> E.global_env_ext -> E.context -> E.context ->
      T.term -> T.term -> E.typ_or_sort -> 'a1 lift_typing -> (T.term -> 'a1
      -> 'a2) -> 'a2 lift_typing **)

  let lift_typing_impl _UU03a3_ _UU03a3_' _UU0393_ _UU0393_' t0 t' t1 hT hPQ =
    lift_judgment_impl _UU03a3_ _UU03a3_' _UU0393_ _UU0393_' t0 t' t1 hT hPQ
      (fun hs ->
      infer_typing_sort_impl _UU03a3_ _UU03a3_' _UU0393_ _UU0393_' t0 t'
        (Obj.magic id) (Obj.magic hs)
        (hPQ (T.tSort (Obj.magic id (projT1 hs)))))

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

  (** val coq_All_local_env_over_gen_rect :
      E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
      lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
      'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
      lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
      'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env
      -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 **)

  let rec coq_All_local_env_over_gen_rect _UU03a3_ f f0 f1 _ _ = function
  | Coq_localenv_over_nil -> f
  | Coq_localenv_over_cons_abs (_UU0393_, na, t0, all, a, tu, hs) ->
    f0 _UU0393_ na t0 all a
      (coq_All_local_env_over_gen_rect _UU03a3_ f f0 f1 _UU0393_ all a) tu hs
  | Coq_localenv_over_cons_def (_UU0393_, na, b, t0, all, tb, a, hc, tu, hs) ->
    f1 _UU0393_ na b t0 all tb a
      (coq_All_local_env_over_gen_rect _UU03a3_ f f0 f1 _UU0393_ all a) hc tu
      hs

  (** val coq_All_local_env_over_gen_rec :
      E.global_env_ext -> 'a5 -> (E.context -> aname -> T.term -> ('a1, 'a2)
      lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
      'a5) -> (E.context -> aname -> T.term -> T.term -> ('a1, 'a2)
      lift_judgment coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
      'a4 -> 'a5) -> E.context -> ('a1, 'a2) lift_judgment coq_All_local_env
      -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 **)

  let rec coq_All_local_env_over_gen_rec _UU03a3_ f f0 f1 _ _ = function
  | Coq_localenv_over_nil -> f
  | Coq_localenv_over_cons_abs (_UU0393_, na, t0, all, a, tu, hs) ->
    f0 _UU0393_ na t0 all a
      (coq_All_local_env_over_gen_rec _UU03a3_ f f0 f1 _UU0393_ all a) tu hs
  | Coq_localenv_over_cons_def (_UU0393_, na, b, t0, all, tb, a, hc, tu, hs) ->
    f1 _UU0393_ na b t0 all tb a
      (coq_All_local_env_over_gen_rec _UU03a3_ f f0 f1 _UU0393_ all a) hc tu
      hs

  type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
    ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

  (** val coq_All_local_env_over_gen_sig_pack :
      E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
      coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
      (E.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
      'a3, 'a4) coq_All_local_env_over_gen **)

  let coq_All_local_env_over_gen_sig_pack _ _UU0393_ x all_local_env_over_gen_var =
    (_UU0393_,x),all_local_env_over_gen_var

  (** val coq_All_local_env_over_gen_Signature :
      E.global_env_ext -> E.context -> ('a1, 'a2) lift_judgment
      coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
      E.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
      'a4) coq_All_local_env_over_gen_sig) coq_Signature **)

  let coq_All_local_env_over_gen_Signature =
    coq_All_local_env_over_gen_sig_pack

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

  (** val ctx_inst_rect :
      E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
      T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
      (aname -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst
      -> 'a2 -> 'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 **)

  let rec ctx_inst_rect _UU03a3_ _UU0393_ f f0 f1 _ _ = function
  | Coq_ctx_inst_nil -> f
  | Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
    f0 na t0 i inst _UU0394_ t1 c
      (ctx_inst_rect _UU03a3_ _UU0393_ f f0 f1 inst
        (E.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_) c)
  | Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
    f1 na b t0 inst _UU0394_ c
      (ctx_inst_rect _UU03a3_ _UU0393_ f f0 f1 inst
        (E.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_) c)

  (** val ctx_inst_rec :
      E.global_env_ext -> E.context -> 'a2 -> (aname -> T.term -> T.term ->
      T.term list -> E.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) ->
      (aname -> T.term -> T.term -> T.term list -> E.context -> 'a1 ctx_inst
      -> 'a2 -> 'a2) -> T.term list -> E.context -> 'a1 ctx_inst -> 'a2 **)

  let rec ctx_inst_rec _UU03a3_ _UU0393_ f f0 f1 _ _ = function
  | Coq_ctx_inst_nil -> f
  | Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
    f0 na t0 i inst _UU0394_ t1 c
      (ctx_inst_rec _UU03a3_ _UU0393_ f f0 f1 inst
        (E.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_) c)
  | Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
    f1 na b t0 inst _UU0394_ c
      (ctx_inst_rec _UU03a3_ _UU0393_ f f0 f1 inst
        (E.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_) c)

  type 'typing ctx_inst_sig = 'typing ctx_inst

  (** val ctx_inst_sig_pack :
      E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1
      ctx_inst -> (T.term list * E.context) * 'a1 ctx_inst **)

  let ctx_inst_sig_pack _ _ x x0 ctx_inst_var =
    (x,x0),ctx_inst_var

  (** val ctx_inst_Signature :
      E.global_env_ext -> E.context -> T.term list -> E.context -> ('a1
      ctx_inst, T.term list * E.context, 'a1 ctx_inst_sig) coq_Signature **)

  let ctx_inst_Signature =
    ctx_inst_sig_pack

  (** val coq_NoConfusionPackage_ctx_inst :
      E.global_env_ext -> E.context -> ((T.term list * E.context) * 'a1
      ctx_inst) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_ctx_inst _ _ =
    Build_NoConfusionPackage

  (** val ctx_inst_impl_gen :
      E.global_env_ext -> E.context -> T.term list -> E.context -> __ list ->
      (__, __ ctx_inst) sigT -> (T.term -> T.term -> (__, __) coq_All -> 'a1)
      -> (__, __ ctx_inst) coq_All -> 'a1 ctx_inst **)

  let ctx_inst_impl_gen _ _ inst _UU0394_ args x hPQ h =
    let Coq_existT (_, c) = x in
    let rec f _ _ c0 h0 =
      match c0 with
      | Coq_ctx_inst_nil -> Coq_ctx_inst_nil
      | Coq_ctx_inst_ass (na, t0, i, inst0, _UU0394_0, _, c1) ->
        Coq_ctx_inst_ass (na, t0, i, inst0, _UU0394_0,
          (hPQ i t0
            (coq_All_impl args h0 (fun _ x0 ->
              match x0 with
              | Coq_ctx_inst_ass (_, _, _, _, _, x1, _) -> x1
              | _ -> assert false (* absurd case *)))),
          (f inst0 (E.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_0) c1
            (coq_All_impl args h0 (fun _ x0 ->
              match x0 with
              | Coq_ctx_inst_ass (_, _, _, _, _, _, x1) -> x1
              | _ -> assert false (* absurd case *)))))
      | Coq_ctx_inst_def (na, b, t0, inst0, _UU0394_0, c1) ->
        Coq_ctx_inst_def (na, b, t0, inst0, _UU0394_0,
          (f inst0 (E.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_0) c1
            (coq_All_impl args h0 (fun _ x0 ->
              match x0 with
              | Coq_ctx_inst_def (_, _, _, _, _, x1) -> x1
              | _ -> assert false (* absurd case *)))))
    in f inst _UU0394_ c h

  (** val ctx_inst_impl :
      E.global_env_ext -> E.context -> T.term list -> E.context -> 'a1
      ctx_inst -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 ctx_inst **)

  let rec ctx_inst_impl _UU03a3_ _UU0393_ _ _ h hPQ =
    match h with
    | Coq_ctx_inst_nil -> Coq_ctx_inst_nil
    | Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
      Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, (hPQ i t0 t1),
        (ctx_inst_impl _UU03a3_ _UU0393_ inst
          (E.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_) c hPQ))
    | Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
      Coq_ctx_inst_def (na, b, t0, inst, _UU0394_,
        (ctx_inst_impl _UU03a3_ _UU0393_ inst
          (E.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_) c hPQ))

  (** val coq_All_local_env_size_gen :
      (E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> 'a1 ->
      size) -> size -> E.global_env_ext -> E.context -> 'a1 coq_All_local_env
      -> size **)

  let rec coq_All_local_env_size_gen psize base _UU03a3_ _ = function
  | Coq_localenv_nil -> base
  | Coq_localenv_cons_abs (_UU0393_', _, t0, w', p) ->
    add (psize _UU03a3_ _UU0393_' t0 Sort p)
      (coq_All_local_env_size_gen psize base _UU03a3_ _UU0393_' w')
  | Coq_localenv_cons_def (_UU0393_', _, b, t0, w', pt, pb) ->
    add
      (add (psize _UU03a3_ _UU0393_' t0 Sort pt)
        (psize _UU03a3_ _UU0393_' b (Typ t0) pb))
      (coq_All_local_env_size_gen psize base _UU03a3_ _UU0393_' w')

  (** val lift_judgment_size :
      (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
      (E.global_env_ext -> E.context -> T.term -> 'a2 -> size) ->
      E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a2)
      lift_judgment -> size **)

  let lift_judgment_size csize ssize _UU03a3_ _UU0393_ t0 t1 w =
    match t1 with
    | Typ t2 -> Obj.magic csize _UU03a3_ _UU0393_ t0 t2 w
    | Sort -> Obj.magic ssize _UU03a3_ _UU0393_ t0 w

  (** val lift_typing_size :
      (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
      E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a1
      infer_sort) lift_judgment -> size **)

  let lift_typing_size typing_size =
    lift_judgment_size typing_size (fun _UU03a3_ _UU0393_ t0 tu ->
      let Coq_existT (s, d) = tu in
      typing_size _UU03a3_ _UU0393_ t0 (T.tSort s) d)

  (** val coq_All_local_env_size :
      (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
      E.global_env_ext -> E.context -> ('a1, 'a1 infer_sort) lift_judgment
      coq_All_local_env -> size **)

  let coq_All_local_env_size typing_size =
    coq_All_local_env_size_gen (lift_typing_size typing_size) O

  (** val coq_All_local_rel_size :
      (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
      E.global_env_ext -> E.context -> E.context -> ('a1, 'a1 infer_sort)
      lift_judgment coq_All_local_rel -> size **)

  let coq_All_local_rel_size typing_size _UU03a3_ _UU0393_ _UU0394_ w =
    coq_All_local_env_size_gen (fun _UU03a3_0 _UU0394_0 ->
      lift_typing_size typing_size _UU03a3_0
        (E.app_context _UU0393_ _UU0394_0)) O _UU03a3_ _UU0394_ w

  (** val lift_sorting_size :
      (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
      (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size)
      -> E.global_env_ext -> E.context -> T.term -> E.typ_or_sort -> ('a1,
      'a2 infer_sort) lift_judgment -> size **)

  let lift_sorting_size checking_size sorting_size =
    lift_judgment_size checking_size (fun _UU03a3_ _UU0393_ t0 tu ->
      let Coq_existT (s, d) = tu in sorting_size _UU03a3_ _UU0393_ t0 s d)

  (** val coq_All_local_env_sorting_size :
      (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
      (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size)
      -> E.global_env_ext -> E.context -> ('a1, 'a2 infer_sort) lift_judgment
      coq_All_local_env -> size **)

  let coq_All_local_env_sorting_size checking_size sorting_size =
    coq_All_local_env_size_gen (lift_sorting_size checking_size sorting_size)
      (S O)

  (** val coq_All_local_rel_sorting_size :
      (E.global_env_ext -> E.context -> T.term -> T.term -> 'a1 -> size) ->
      (E.global_env_ext -> E.context -> T.term -> Universe.t -> 'a2 -> size)
      -> E.global_env_ext -> E.context -> E.context -> ('a1, 'a2 infer_sort)
      lift_judgment coq_All_local_rel -> size **)

  let coq_All_local_rel_sorting_size checking_size sorting_size _UU03a3_ _UU0393_ _UU0394_ w =
    coq_All_local_env_size_gen (fun _UU03a3_0 _UU0394_0 ->
      lift_sorting_size checking_size sorting_size _UU03a3_0
        (E.app_context _UU0393_ _UU0394_0)) (S O) _UU03a3_ _UU0394_ w
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

module Conversion =
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
 struct
  type 'p coq_All_decls_alpha_pb =
  | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
     * T.term * T.term * 'p
  | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
     * T.term * T.term * T.term * T.term * 'p * 'p

  (** val coq_All_decls_alpha_pb_rect :
      conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term
      -> __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot ->
      T.term -> T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) ->
      T.term context_decl -> T.term context_decl -> 'a1
      coq_All_decls_alpha_pb -> 'a2 **)

  let coq_All_decls_alpha_pb_rect _ f f0 _ _ = function
  | Coq_all_decls_alpha_vass (na, na', t0, t', eqt) -> f na na' t0 t' __ eqt
  | Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
    f0 na na' b t0 b' t' __ eqb eqt

  (** val coq_All_decls_alpha_pb_rec :
      conv_pb -> (name binder_annot -> name binder_annot -> T.term -> T.term
      -> __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot ->
      T.term -> T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) ->
      T.term context_decl -> T.term context_decl -> 'a1
      coq_All_decls_alpha_pb -> 'a2 **)

  let coq_All_decls_alpha_pb_rec _ f f0 _ _ = function
  | Coq_all_decls_alpha_vass (na, na', t0, t', eqt) -> f na na' t0 t' __ eqt
  | Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
    f0 na na' b t0 b' t' __ eqb eqt

  type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

  (** val coq_All_decls_alpha_pb_sig_pack :
      conv_pb -> T.term context_decl -> T.term context_decl -> 'a1
      coq_All_decls_alpha_pb -> (T.term context_decl * T.term
      context_decl) * 'a1 coq_All_decls_alpha_pb **)

  let coq_All_decls_alpha_pb_sig_pack _ x x0 all_decls_alpha_pb_var =
    (x,x0),all_decls_alpha_pb_var

  (** val coq_All_decls_alpha_pb_Signature :
      conv_pb -> T.term context_decl -> T.term context_decl -> ('a1
      coq_All_decls_alpha_pb, T.term context_decl * T.term context_decl, 'a1
      coq_All_decls_alpha_pb_sig) coq_Signature **)

  let coq_All_decls_alpha_pb_Signature =
    coq_All_decls_alpha_pb_sig_pack

  (** val coq_NoConfusionPackage_All_decls_alpha_pb :
      conv_pb -> ((T.term context_decl * T.term context_decl) * 'a1
      coq_All_decls_alpha_pb) coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_All_decls_alpha_pb _ =
    Build_NoConfusionPackage

  type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

  type 'cumul_gen cumul_pb_context =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  type 'cumul_gen cumul_ctx_rel =
    (T.term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

  (** val coq_All_decls_alpha_pb_impl :
      conv_pb -> T.term context_decl -> T.term context_decl -> (conv_pb ->
      T.term -> T.term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
      coq_All_decls_alpha_pb **)

  let coq_All_decls_alpha_pb_impl pb _ _ x = function
  | Coq_all_decls_alpha_vass (na, na', t0, t', eqt) ->
    Coq_all_decls_alpha_vass (na, na', t0, t', (x pb t0 t' eqt))
  | Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
    Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', (x Conv b b' eqb),
      (x pb t0 t' eqt))
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

module GlobalMaps =
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
 struct
  type 'p on_context = 'p ET.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  (** val univs_ext_constraints :
      ConstraintSet.t -> universes_decl -> ConstraintSet.t **)

  let univs_ext_constraints univs _UU03c6_ =
    ConstraintSet.union (constraints_of_udecl _UU03c6_) univs

  (** val ind_realargs : E.one_inductive_body -> nat **)

  let ind_realargs o =
    match TU.destArity Coq_nil (E.ind_type o) with
    | Some p ->
      let Coq_pair (ctx, _) = p in length (E.smash_context Coq_nil ctx)
    | None -> O

  type positive_cstr_arg =
  | Coq_pos_arg_closed of T.term
  | Coq_pos_arg_concl of T.term list * nat * E.one_inductive_body
     * (T.term, __) coq_All
  | Coq_pos_arg_let of aname * T.term * T.term * T.term * positive_cstr_arg
  | Coq_pos_arg_ass of aname * T.term * T.term * positive_cstr_arg

  (** val positive_cstr_arg_rect :
      E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
      'a1) -> (T.term context_decl list -> T.term list -> nat ->
      E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
      positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname
      -> T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr_arg -> 'a1 **)

  let rec positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_ _ = function
  | Coq_pos_arg_closed ty -> f _UU0393_ ty __
  | Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
  | Coq_pos_arg_let (na, b, ty, ty', p0) ->
    f1 _UU0393_ na b ty ty' p0
      (positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_
        (T.subst (Coq_cons (b, Coq_nil)) O ty') p0)
  | Coq_pos_arg_ass (na, ty, ty', p0) ->
    f2 _UU0393_ na ty ty' __ p0
      (positive_cstr_arg_rect mdecl f f0 f1 f2 (Coq_cons ((E.vass na ty),
        _UU0393_)) ty' p0)

  (** val positive_cstr_arg_rec :
      E.mutual_inductive_body -> (T.term context_decl list -> T.term -> __ ->
      'a1) -> (T.term context_decl list -> T.term list -> nat ->
      E.one_inductive_body -> __ -> (T.term, __) coq_All -> __ -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term -> T.term ->
      positive_cstr_arg -> 'a1 -> 'a1) -> (T.term context_decl list -> aname
      -> T.term -> T.term -> __ -> positive_cstr_arg -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr_arg -> 'a1 **)

  let rec positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_ _ = function
  | Coq_pos_arg_closed ty -> f _UU0393_ ty __
  | Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
  | Coq_pos_arg_let (na, b, ty, ty', p0) ->
    f1 _UU0393_ na b ty ty' p0
      (positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_
        (T.subst (Coq_cons (b, Coq_nil)) O ty') p0)
  | Coq_pos_arg_ass (na, ty, ty', p0) ->
    f2 _UU0393_ na ty ty' __ p0
      (positive_cstr_arg_rec mdecl f f0 f1 f2 (Coq_cons ((E.vass na ty),
        _UU0393_)) ty' p0)

  type positive_cstr =
  | Coq_pos_concl of T.term list * (T.term, __) coq_All
  | Coq_pos_let of aname * T.term * T.term * T.term * positive_cstr
  | Coq_pos_ass of aname * T.term * T.term * positive_cstr_arg * positive_cstr

  (** val positive_cstr_rect :
      E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
      list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
      aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term ->
      positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr -> 'a1 **)

  let rec positive_cstr_rect mdecl i f f0 f1 _UU0393_ _ = function
  | Coq_pos_concl (l, x) -> f _UU0393_ l x
  | Coq_pos_let (na, b, ty, ty', p0) ->
    f0 _UU0393_ na b ty ty' p0
      (positive_cstr_rect mdecl i f f0 f1 _UU0393_
        (T.subst (Coq_cons (b, Coq_nil)) O ty') p0)
  | Coq_pos_ass (na, ty, ty', p0, p1) ->
    f1 _UU0393_ na ty ty' p0 p1
      (positive_cstr_rect mdecl i f f0 f1 (Coq_cons ((E.vass na ty),
        _UU0393_)) ty' p1)

  (** val positive_cstr_rec :
      E.mutual_inductive_body -> nat -> (T.term context_decl list -> T.term
      list -> (T.term, __) coq_All -> 'a1) -> (T.term context_decl list ->
      aname -> T.term -> T.term -> T.term -> positive_cstr -> 'a1 -> 'a1) ->
      (T.term context_decl list -> aname -> T.term -> T.term ->
      positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) -> T.term
      context_decl list -> T.term -> positive_cstr -> 'a1 **)

  let rec positive_cstr_rec mdecl i f f0 f1 _UU0393_ _ = function
  | Coq_pos_concl (l, x) -> f _UU0393_ l x
  | Coq_pos_let (na, b, ty, ty', p0) ->
    f0 _UU0393_ na b ty ty' p0
      (positive_cstr_rec mdecl i f f0 f1 _UU0393_
        (T.subst (Coq_cons (b, Coq_nil)) O ty') p0)
  | Coq_pos_ass (na, ty, ty', p0, p1) ->
    f1 _UU0393_ na ty ty' p0 p1
      (positive_cstr_rec mdecl i f f0 f1 (Coq_cons ((E.vass na ty),
        _UU0393_)) ty' p1)

  (** val lift_level : nat -> Level.t_ -> Level.t_ **)

  let lift_level n l = match l with
  | Level.Coq_lvar k -> Level.Coq_lvar (add n k)
  | _ -> l

  (** val lift_instance : nat -> Level.t_ list -> Level.t_ list **)

  let lift_instance n l =
    map (lift_level n) l

  (** val lift_constraint :
      nat -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t_,
      ConstraintType.t) prod, Level.t_) prod **)

  let lift_constraint n = function
  | Coq_pair (p, l') ->
    let Coq_pair (l, r) = p in
    Coq_pair ((Coq_pair ((lift_level n l), r)), (lift_level n l'))

  (** val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t **)

  let lift_constraints n cstrs =
    ConstraintSet.fold (fun elt acc ->
      ConstraintSet.add (lift_constraint n elt) acc) cstrs ConstraintSet.empty

  (** val level_var_instance : nat -> name list -> Level.t_ list **)

  let level_var_instance n inst =
    mapi_rec (fun i _ -> Level.Coq_lvar i) inst n

  (** val variance_cstrs :
      Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t **)

  let rec variance_cstrs v u u' =
    match v with
    | Coq_nil -> ConstraintSet.empty
    | Coq_cons (v0, vs) ->
      (match u with
       | Coq_nil -> ConstraintSet.empty
       | Coq_cons (u0, us) ->
         (match u' with
          | Coq_nil -> ConstraintSet.empty
          | Coq_cons (u'0, us') ->
            (match v0 with
             | Variance.Irrelevant -> variance_cstrs vs us us'
             | Variance.Covariant ->
               ConstraintSet.add (Coq_pair ((Coq_pair (u0, (ConstraintType.Le
                 Z0))), u'0)) (variance_cstrs vs us us')
             | Variance.Invariant ->
               ConstraintSet.add (Coq_pair ((Coq_pair (u0,
                 ConstraintType.Eq)), u'0)) (variance_cstrs vs us us'))))

  (** val variance_universes :
      universes_decl -> Variance.t list -> ((universes_decl, Level.t_ list)
      prod, Level.t_ list) prod option **)

  let variance_universes univs v =
    match univs with
    | Monomorphic_ctx -> None
    | Polymorphic_ctx auctx ->
      let Coq_pair (inst, cstrs) = auctx in
      let u' = level_var_instance O inst in
      let u = lift_instance (length inst) u' in
      let cstrs0 =
        ConstraintSet.union cstrs (lift_constraints (length inst) cstrs)
      in
      let cstrv = variance_cstrs v u u' in
      let auctx' = Coq_pair ((app inst inst),
        (ConstraintSet.union cstrs0 cstrv))
      in
      Some (Coq_pair ((Coq_pair ((Polymorphic_ctx auctx'), u)), u'))

  (** val ind_arities :
      E.mutual_inductive_body -> T.term context_decl list **)

  let ind_arities mdecl =
    E.arities_context (E.ind_bodies mdecl)

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  (** val cstr_concl_head :
      E.mutual_inductive_body -> nat -> E.constructor_body -> T.term **)

  let cstr_concl_head mdecl i cdecl =
    T.tRel
      (add
        (add (sub (length (E.ind_bodies mdecl)) (S i))
          (length (E.ind_params mdecl))) (length (E.cstr_args cdecl)))

  (** val cstr_concl :
      E.mutual_inductive_body -> nat -> E.constructor_body -> T.term **)

  let cstr_concl mdecl i cdecl =
    T.mkApps (cstr_concl_head mdecl i cdecl)
      (app
        (E.to_extended_list_k (E.ind_params mdecl)
          (length (E.cstr_args cdecl))) (E.cstr_indices cdecl))

  type ('pcmp, 'p) on_constructor = { on_ctype : 'p on_type;
                                      on_cargs : 'p sorts_local_ctx;
                                      on_cindices : 'p ET.ctx_inst;
                                      on_ctype_positive : positive_cstr;
                                      on_ctype_variance : (Variance.t list ->
                                                          __ -> 'pcmp
                                                          cstr_respects_variance) }

  (** val on_ctype :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
      list -> ('a1, 'a2) on_constructor -> 'a2 on_type **)

  let on_ctype _ _ _ _ _ _ _ _ o =
    o.on_ctype

  (** val on_cargs :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
      list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx **)

  let on_cargs _ _ _ _ _ _ _ _ o =
    o.on_cargs

  (** val on_cindices :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
      list -> ('a1, 'a2) on_constructor -> 'a2 ET.ctx_inst **)

  let on_cindices _ _ _ _ _ _ _ _ o =
    o.on_cindices

  (** val on_ctype_positive :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
      list -> ('a1, 'a2) on_constructor -> positive_cstr **)

  let on_ctype_positive _ _ _ _ _ _ _ _ o =
    o.on_ctype_positive

  (** val on_ctype_variance :
      checker_flags -> E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
      list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
      cstr_respects_variance **)

  let on_ctype_variance _ _ _ _ _ _ _ _ o v =
    o.on_ctype_variance v __

  type ('pcmp, 'p) on_constructors =
    (E.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor) coq_All2

  type on_projections =
    (E.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  (** val on_projs :
      E.mutual_inductive_body -> kername -> nat -> E.one_inductive_body ->
      E.context -> E.constructor_body -> on_projections ->
      (E.projection_body, __) coq_Alli **)

  let on_projs _ _ _ _ _ _ o =
    o

  type constructor_univs = Universe.t list

  (** val elim_sort_prop_ind :
      constructor_univs list -> allowed_eliminations **)

  let elim_sort_prop_ind = function
  | Coq_nil -> IntoAny
  | Coq_cons (s, l) ->
    (match l with
     | Coq_nil ->
       (match forallb is_propositional s with
        | Coq_true -> IntoAny
        | Coq_false -> IntoPropSProp)
     | Coq_cons (_, _) -> IntoPropSProp)

  (** val elim_sort_sprop_ind :
      constructor_univs list -> allowed_eliminations **)

  let elim_sort_sprop_ind = function
  | Coq_nil -> IntoAny
  | Coq_cons (_, _) -> IntoSProp

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = { onArity : 'p on_type;
                                   ind_cunivs : constructor_univs list;
                                   onConstructors : ('pcmp, 'p)
                                                    on_constructors;
                                   onProjections : __;
                                   ind_sorts : 'p check_ind_sorts;
                                   onIndices : __ }

  (** val onArity :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2 on_type **)

  let onArity _ _ _ _ _ _ o =
    o.onArity

  (** val ind_cunivs :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body ->
      constructor_univs list **)

  let ind_cunivs _ _ _ _ _ _ o =
    o.ind_cunivs

  (** val onConstructors :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1, 'a2)
      on_constructors **)

  let onConstructors _ _ _ _ _ _ o =
    o.onConstructors

  (** val onProjections :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __ **)

  let onProjections _ _ _ _ _ _ o =
    o.onProjections

  (** val ind_sorts :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
      check_ind_sorts **)

  let ind_sorts _ _ _ _ _ _ o =
    o.ind_sorts

  (** val onIndices :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> nat -> E.one_inductive_body -> ('a1, 'a2) on_ind_body -> __ **)

  let onIndices _ _ _ _ _ _ o =
    o.onIndices

  type on_variance = __

  type ('pcmp, 'p) on_inductive = { onInductives : (E.one_inductive_body,
                                                   ('pcmp, 'p) on_ind_body)
                                                   coq_Alli;
                                    onParams : 'p on_context;
                                    onVariance : on_variance }

  (** val onInductives :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> ('a1, 'a2) on_inductive -> (E.one_inductive_body, ('a1, 'a2)
      on_ind_body) coq_Alli **)

  let onInductives _ _ _ _ o =
    o.onInductives

  (** val onParams :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> ('a1, 'a2) on_inductive -> 'a2 on_context **)

  let onParams _ _ _ _ o =
    o.onParams

  (** val onVariance :
      checker_flags -> E.global_env_ext -> kername -> E.mutual_inductive_body
      -> ('a1, 'a2) on_inductive -> on_variance **)

  let onVariance _ _ _ _ o =
    o.onVariance

  type 'p on_constant_decl = __

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  (** val udecl :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls_data -> universes_decl **)

  let udecl _ _ _ _ _ d _ =
    L.universes_decl_of_decl d

  (** val on_global_decl_d :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls_data -> ('a1, 'a2) on_global_decl **)

  let on_global_decl_d _ _ _ _ _ _ o =
    o

  type ('pcmp, 'p) on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of E.global_declarations * kername * E.global_decl
     * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

  (** val on_global_decls_rect :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
      (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
      E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

  let rec on_global_decls_rect cf univs retro f f0 _ = function
  | Coq_globenv_nil -> f
  | Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
    f0 _UU03a3_ kn d o0
      (on_global_decls_rect cf univs retro f f0 _UU03a3_ o0) o1

  (** val on_global_decls_rec :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
      (E.global_declarations -> kername -> E.global_decl -> ('a1, 'a2)
      on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
      E.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

  let rec on_global_decls_rec cf univs retro f f0 _ = function
  | Coq_globenv_nil -> f
  | Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
    f0 _UU03a3_ kn d o0 (on_global_decls_rec cf univs retro f f0 _UU03a3_ o0)
      o1

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  (** val on_global_decls_sig_pack :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> ('a1, 'a2) on_global_decls ->
      E.global_declarations * ('a1, 'a2) on_global_decls **)

  let on_global_decls_sig_pack _ _ _ x on_global_decls_var =
    x,on_global_decls_var

  (** val on_global_decls_Signature :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      E.global_declarations -> (('a1, 'a2) on_global_decls,
      E.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature **)

  let on_global_decls_Signature =
    on_global_decls_sig_pack

  type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

  type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

  (** val type_local_ctx_impl_gen :
      E.global_env_ext -> E.context -> E.context -> Universe.t -> __ list ->
      (__, __ type_local_ctx) sigT -> (E.context -> T.term -> E.typ_or_sort
      -> (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx) coq_All -> 'a1
      type_local_ctx **)

  let rec type_local_ctx_impl_gen _UU03a3_ _UU0393_ _UU0394_ u args hexists hP hPQ =
    match _UU0394_ with
    | Coq_nil -> Obj.magic __ _UU0393_ hPQ hP hexists
    | Coq_cons (y, l) ->
      let iH_UU0394_ = fun h1 _UU0393_0 h2 h ->
        type_local_ctx_impl_gen _UU03a3_ _UU0393_0 l u args (Coq_existT (__,
          h2)) h1 h
      in
      let iH_UU0394_0 = fun _UU0393_0 h2 -> iH_UU0394_ hP _UU0393_0 h2 in
      let Coq_existT (_, y0) = hexists in
      let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } =
        y
      in
      (match decl_body0 with
       | Some t0 ->
         let Coq_pair (t1, _) = Obj.magic y0 in
         Obj.magic (Coq_pair
           ((iH_UU0394_0 _UU0393_ t1
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let Coq_pair (t2, _) = x in t2))), (Coq_pair
           ((hP (E.app_context _UU0393_ l) decl_type0 Sort
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let Coq_pair (_, p) = x in let Coq_pair (x0, _) = p in x0))),
           (hP (E.app_context _UU0393_ l) t0 (Typ decl_type0)
             (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
               let Coq_pair (_, p) = x in let Coq_pair (_, x0) = p in x0)))))))
       | None ->
         let Coq_pair (t0, _) = Obj.magic y0 in
         Obj.magic (Coq_pair
           ((iH_UU0394_0 _UU0393_ t0
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let Coq_pair (t1, _) = x in t1))),
           (hP (E.app_context _UU0393_ l) decl_type0 (Typ (T.tSort u))
             (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
               let Coq_pair (_, x0) = x in x0))))))

  (** val type_local_ctx_impl :
      E.global_env_ext -> E.context -> E.context -> Universe.t -> 'a1
      type_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2)
      -> 'a2 type_local_ctx **)

  let rec type_local_ctx_impl _UU03a3_ _UU0393_ _UU0394_ u hP hPQ =
    match _UU0394_ with
    | Coq_nil -> Obj.magic __ _UU0393_ hPQ hP
    | Coq_cons (y, l) ->
      let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } =
        y
      in
      (match decl_body0 with
       | Some t0 ->
         let Coq_pair (a, b) = Obj.magic hP in
         let Coq_pair (a0, b0) = b in
         Obj.magic (Coq_pair
           ((type_local_ctx_impl _UU03a3_ _UU0393_ l u a hPQ), (Coq_pair
           ((hPQ (E.app_context _UU0393_ l) decl_type0 Sort a0),
           (hPQ (E.app_context _UU0393_ l) t0 (Typ decl_type0) b0)))))
       | None ->
         let Coq_pair (a, b) = Obj.magic hP in
         Obj.magic (Coq_pair
           ((type_local_ctx_impl _UU03a3_ _UU0393_ l u a hPQ),
           (hPQ (E.app_context _UU0393_ l) decl_type0 (Typ (T.tSort u)) b))))

  (** val sorts_local_ctx_impl_gen :
      E.global_env_ext -> E.context -> E.context -> Universe.t list -> __
      list -> (__, __ sorts_local_ctx) sigT -> (E.context -> T.term ->
      E.typ_or_sort -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx)
      coq_All -> 'a1 sorts_local_ctx **)

  let rec sorts_local_ctx_impl_gen _UU03a3_ _UU0393_ _UU0394_ u args hexists hP hPQ =
    match _UU0394_ with
    | Coq_nil -> let Coq_existT (_, y) = hexists in y
    | Coq_cons (y, l) ->
      let iH_UU0394_ = fun h1 _UU0393_0 u0 h2 h ->
        sorts_local_ctx_impl_gen _UU03a3_ _UU0393_0 l u0 args (Coq_existT
          (__, h2)) h1 h
      in
      let iH_UU0394_0 = fun _UU0393_0 u0 h2 -> iH_UU0394_ hP _UU0393_0 u0 h2
      in
      let Coq_existT (_, y0) = hexists in
      let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } =
        y
      in
      (match decl_body0 with
       | Some t0 ->
         let Coq_pair (s, _) = Obj.magic y0 in
         Obj.magic (Coq_pair
           ((iH_UU0394_0 _UU0393_ u s
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let Coq_pair (s0, _) = x in s0))), (Coq_pair
           ((hP (E.app_context _UU0393_ l) decl_type0 Sort
              (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                let Coq_pair (_, p) = x in let Coq_pair (x0, _) = p in x0))),
           (hP (E.app_context _UU0393_ l) t0 (Typ decl_type0)
             (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
               let Coq_pair (_, p) = x in let Coq_pair (_, x0) = p in x0)))))))
       | None ->
         (match u with
          | Coq_nil -> Obj.magic __ hPQ y0
          | Coq_cons (t0, l0) ->
            let Coq_pair (s, _) = Obj.magic y0 in
            Obj.magic (Coq_pair
              ((iH_UU0394_0 _UU0393_ l0 s
                 (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                   let Coq_pair (s0, _) = x in s0))),
              (hP (E.app_context _UU0393_ l) decl_type0 (Typ (T.tSort t0))
                (coq_All_impl args (Obj.magic hPQ) (fun _ x ->
                  let Coq_pair (_, x0) = x in x0)))))))

  (** val sorts_local_ctx_impl :
      E.global_env_ext -> E.context -> E.context -> Universe.t list -> 'a1
      sorts_local_ctx -> (E.context -> T.term -> E.typ_or_sort -> 'a1 -> 'a2)
      -> 'a2 sorts_local_ctx **)

  let rec sorts_local_ctx_impl _UU03a3_ _UU0393_ _UU0394_ u hP hPQ =
    match _UU0394_ with
    | Coq_nil -> hP
    | Coq_cons (y, l) ->
      let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } =
        y
      in
      (match decl_body0 with
       | Some t0 ->
         let Coq_pair (a, b) = Obj.magic hP in
         let Coq_pair (a0, b0) = b in
         Obj.magic (Coq_pair
           ((sorts_local_ctx_impl _UU03a3_ _UU0393_ l u a hPQ), (Coq_pair
           ((hPQ (E.app_context _UU0393_ l) decl_type0 Sort a0),
           (hPQ (E.app_context _UU0393_ l) t0 (Typ decl_type0) b0)))))
       | None ->
         (match u with
          | Coq_nil -> Obj.magic __ hP
          | Coq_cons (t0, l0) ->
            let Coq_pair (a, b) = Obj.magic hP in
            Obj.magic (Coq_pair
              ((sorts_local_ctx_impl _UU03a3_ _UU0393_ l l0 a hPQ),
              (hPQ (E.app_context _UU0393_ l) decl_type0 (Typ (T.tSort t0)) b)))))

  (** val cstr_respects_variance_impl_gen :
      E.global_env -> E.mutual_inductive_body -> Variance.t list ->
      E.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT
      -> __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
      cstr_respects_variance **)

  let cstr_respects_variance_impl_gen _ mdecl v cs args =
    let o = variance_universes (E.ind_universes mdecl) v in
    (match o with
     | Some p ->
       (fun hexists hPQ hP ->
         let Coq_pair (p0, l) = p in
         let Coq_pair (_, l0) = p0 in
         let hP0 = coq_All_prod_inv args (Obj.magic hP) in
         let Coq_pair (a, a0) = hP0 in
         let hP1 =
           coq_All_All2_fold_swap_sum args
             (subst_instance E.subst_instance_context l0
               (E.expand_lets_ctx (E.ind_params mdecl)
                 (E.smash_context Coq_nil (E.cstr_args cs))))
             (subst_instance E.subst_instance_context l
               (E.expand_lets_ctx (E.ind_params mdecl)
                 (E.smash_context Coq_nil (E.cstr_args cs)))) a
         in
         let hP2 =
           coq_All_All2_swap_sum args
             (map (fun x ->
               subst_instance T.subst_instance_constr l0
                 (E.expand_lets
                   (E.app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs))
             (map (fun x ->
               subst_instance T.subst_instance_constr l
                 (E.expand_lets
                   (E.app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs)) a0
         in
         (match args with
          | Coq_nil ->
            let hPQ0 = fun _UU0393_ t0 t1 pb ->
              Obj.magic hPQ _UU0393_ t0 t1 pb All_nil
            in
            let Coq_existT (_, p1) = hexists in
            let Coq_pair (a1, a2) = Obj.magic p1 in
            Obj.magic (Coq_pair
              ((coq_All2_fold_impl
                 (subst_instance E.subst_instance_context l0
                   (E.expand_lets_ctx (E.ind_params mdecl)
                     (E.smash_context Coq_nil (E.cstr_args cs))))
                 (subst_instance E.subst_instance_context l
                   (E.expand_lets_ctx (E.ind_params mdecl)
                     (E.smash_context Coq_nil (E.cstr_args cs)))) a1
                 (fun _UU0393_ _ d d' ->
                 C.coq_All_decls_alpha_pb_impl Cumul d d' (fun pb t0 t' _ ->
                   hPQ0
                     (E.app_context
                       (subst_instance E.subst_instance_context l0
                         (E.app_context (ind_arities mdecl)
                           (E.smash_context Coq_nil (E.ind_params mdecl))))
                       _UU0393_) t0 t' pb))),
              (coq_All2_impl
                (map (fun x ->
                  subst_instance T.subst_instance_constr l0
                    (E.expand_lets
                      (E.app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
                  (E.cstr_indices cs))
                (map (fun x ->
                  subst_instance T.subst_instance_constr l
                    (E.expand_lets
                      (E.app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
                  (E.cstr_indices cs)) a2 (fun x y _ ->
                hPQ0
                  (subst_instance E.subst_instance_context l0
                    (E.app_context (ind_arities mdecl)
                      (E.smash_context Coq_nil
                        (E.app_context (E.ind_params mdecl) (E.cstr_args cs)))))
                  x y Conv))))
          | Coq_cons (_, l1) ->
            (match hP1 with
             | Coq_inl _ -> assert false (* absurd case *)
             | Coq_inr a1 ->
               (match hP2 with
                | Coq_inl _ -> assert false (* absurd case *)
                | Coq_inr a2 ->
                  Obj.magic (Coq_pair
                    ((coq_All2_fold_impl
                       (subst_instance E.subst_instance_context l0
                         (E.expand_lets_ctx (E.ind_params mdecl)
                           (E.smash_context Coq_nil (E.cstr_args cs))))
                       (subst_instance E.subst_instance_context l
                         (E.expand_lets_ctx (E.ind_params mdecl)
                           (E.smash_context Coq_nil (E.cstr_args cs)))) a1
                       (fun _UU0393_ _ _ _ x ->
                       match x with
                       | All_nil -> assert false (* absurd case *)
                       | All_cons (_, _, x0, x1) ->
                         (match x0 with
                          | C.Coq_all_decls_alpha_vass (na, na', t0, t', eqt) ->
                            C.Coq_all_decls_alpha_vass (na, na', t0, t',
                              (Obj.magic hPQ
                                (E.app_context
                                  (subst_instance E.subst_instance_context l0
                                    (E.app_context (ind_arities mdecl)
                                      (E.smash_context Coq_nil
                                        (E.ind_params mdecl)))) _UU0393_) t0
                                t' Cumul (All_cons (__, l1, eqt,
                                (coq_All_impl l1 x1 (fun _ x2 ->
                                  match x2 with
                                  | C.Coq_all_decls_alpha_vass (_, _, _, _,
                                                                eqt0) ->
                                    eqt0
                                  | C.Coq_all_decls_alpha_vdef (_, _, _, _,
                                                                _, _, _, _) ->
                                    assert false (* absurd case *)))))))
                          | C.Coq_all_decls_alpha_vdef (na, na', b, t0, b',
                                                        t', eqb, eqt) ->
                            C.Coq_all_decls_alpha_vdef (na, na', b, t0, b',
                              t',
                              (Obj.magic hPQ
                                (E.app_context
                                  (subst_instance E.subst_instance_context l0
                                    (E.app_context (ind_arities mdecl)
                                      (E.smash_context Coq_nil
                                        (E.ind_params mdecl)))) _UU0393_) b
                                b' Conv (All_cons (__, l1, eqb,
                                (coq_All_impl l1 x1 (fun _ x2 ->
                                  match x2 with
                                  | C.Coq_all_decls_alpha_vass (_, _, _, _, _) ->
                                    assert false (* absurd case *)
                                  | C.Coq_all_decls_alpha_vdef (_, _, _, _,
                                                                _, _, eqb0, _) ->
                                    eqb0))))),
                              (Obj.magic hPQ
                                (E.app_context
                                  (subst_instance E.subst_instance_context l0
                                    (E.app_context (ind_arities mdecl)
                                      (E.smash_context Coq_nil
                                        (E.ind_params mdecl)))) _UU0393_) t0
                                t' Cumul (All_cons (__, l1, eqt,
                                (coq_All_impl l1 x1 (fun _ x2 ->
                                  match x2 with
                                  | C.Coq_all_decls_alpha_vass (_, _, _, _, _) ->
                                    assert false (* absurd case *)
                                  | C.Coq_all_decls_alpha_vdef (_, _, _, _,
                                                                _, _, _, eqt0) ->
                                    eqt0))))))))),
                    (coq_All2_impl
                      (map (fun x ->
                        subst_instance T.subst_instance_constr l0
                          (E.expand_lets
                            (E.app_context (E.ind_params mdecl)
                              (E.cstr_args cs)) x)) (E.cstr_indices cs))
                      (map (fun x ->
                        subst_instance T.subst_instance_constr l
                          (E.expand_lets
                            (E.app_context (E.ind_params mdecl)
                              (E.cstr_args cs)) x)) (E.cstr_indices cs)) a2
                      (fun x y x0 ->
                      Obj.magic hPQ
                        (subst_instance E.subst_instance_context l0
                          (E.app_context (ind_arities mdecl)
                            (E.smash_context Coq_nil
                              (E.app_context (E.ind_params mdecl)
                                (E.cstr_args cs))))) x y Conv x0))))))))
     | None -> Obj.magic __)

  (** val cstr_respects_variance_impl :
      E.global_env -> E.mutual_inductive_body -> Variance.t list ->
      E.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
      cstr_respects_variance **)

  let cstr_respects_variance_impl _ mdecl v cs =
    let o = variance_universes (E.ind_universes mdecl) v in
    (match o with
     | Some p ->
       (fun hPQ __top_assumption_ ->
         let Coq_pair (p0, l) = p in
         let Coq_pair (_, l0) = p0 in
         let _evar_0_ = fun hP1 hP2 -> Coq_pair
           ((coq_All2_fold_impl
              (subst_instance E.subst_instance_context l0
                (E.expand_lets_ctx (E.ind_params mdecl)
                  (E.smash_context Coq_nil (E.cstr_args cs))))
              (subst_instance E.subst_instance_context l
                (E.expand_lets_ctx (E.ind_params mdecl)
                  (E.smash_context Coq_nil (E.cstr_args cs)))) hP1
              (fun _UU0393_ _ d d' ->
              C.coq_All_decls_alpha_pb_impl Cumul d d' (fun pb t0 t' x ->
                Obj.magic hPQ
                  (E.app_context
                    (subst_instance E.subst_instance_context l0
                      (E.app_context (ind_arities mdecl)
                        (E.smash_context Coq_nil (E.ind_params mdecl))))
                    _UU0393_) t0 t' pb x))),
           (coq_All2_impl
             (map (fun x ->
               subst_instance T.subst_instance_constr l0
                 (E.expand_lets
                   (E.app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs))
             (map (fun x ->
               subst_instance T.subst_instance_constr l
                 (E.expand_lets
                   (E.app_context (E.ind_params mdecl) (E.cstr_args cs)) x))
               (E.cstr_indices cs)) hP2 (fun x y x0 ->
             Obj.magic hPQ
               (subst_instance E.subst_instance_context l0
                 (E.app_context (ind_arities mdecl)
                   (E.smash_context Coq_nil
                     (E.app_context (E.ind_params mdecl) (E.cstr_args cs)))))
               x y Conv x0)))
         in
         let Coq_pair (a, b) = Obj.magic __top_assumption_ in
         Obj.magic _evar_0_ a b)
     | None -> Obj.magic __)

  (** val on_constructor_impl_config_gen :
      E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body -> Universe.t
      list -> ((checker_flags, __) prod, __) prod list -> checker_flags ->
      (((checker_flags, __) prod, __) prod, __) sigT -> (E.context -> T.term
      -> E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All
      -> 'a2) -> (universes_decl -> E.context -> T.term -> T.term -> conv_pb
      -> (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
      (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
      on_constructor **)

  let on_constructor_impl_config_gen _UU03a3_ mdecl _ _ ind_indices0 cdecl cunivs args _ hexists h1 h2 hargs =
    let Coq_existT (_, y) = hexists in
    let Coq_pair (_, o) = Obj.magic y in
    let { on_ctype = _; on_cargs = on_cargs0; on_cindices = on_cindices0;
      on_ctype_positive = on_ctype_positive0; on_ctype_variance =
      on_ctype_variance0 } = o
    in
    { on_ctype =
    (h1 (E.arities_context (E.ind_bodies mdecl)) (E.cstr_type cdecl) Sort
      (coq_All_impl args (Obj.magic hargs) (fun _ x -> x.on_ctype)));
    on_cargs =
    (sorts_local_ctx_impl_gen _UU03a3_
      (E.app_context (E.arities_context (E.ind_bodies mdecl))
        (E.ind_params mdecl)) (E.cstr_args cdecl) cunivs
      (map (Obj.magic __) args) (Coq_existT (__, on_cargs0))
      (fun _UU0393_ t0 t1 x ->
      h1 _UU0393_ t0 t1
        (let Coq_pair (_, x0) = coq_All_eta3 args in
         x0 (coq_All_map_inv (Obj.magic __) args x)))
      (coq_All_map (Obj.magic __) args
        (coq_All_impl args (Obj.magic hargs) (fun _ x -> x.on_cargs))));
    on_cindices =
    (ET.ctx_inst_impl_gen _UU03a3_
      (E.app_context
        (E.app_context (E.arities_context (E.ind_bodies mdecl))
          (E.ind_params mdecl)) (E.cstr_args cdecl)) (E.cstr_indices cdecl)
      (List.rev (E.lift_context (length (E.cstr_args cdecl)) O ind_indices0))
      (map (Obj.magic __) args) (Coq_existT (__, on_cindices0))
      (fun t0 t1 x ->
      h1
        (E.app_context
          (E.app_context (E.arities_context (E.ind_bodies mdecl))
            (E.ind_params mdecl)) (E.cstr_args cdecl)) t0 (Typ t1)
        (let Coq_pair (_, x0) = coq_All_eta3 args in
         x0 (coq_All_map_inv (Obj.magic __) args x)))
      (coq_All_map (Obj.magic __) args
        (coq_All_impl args (Obj.magic hargs) (fun _ x -> x.on_cindices))));
    on_ctype_positive = on_ctype_positive0; on_ctype_variance = (fun _v_ _ ->
    let on_ctype_variance1 = on_ctype_variance0 _v_ __ in
    cstr_respects_variance_impl_gen (E.fst_ctx _UU03a3_) mdecl _v_ cdecl
      (map (Obj.magic __) args) (Coq_existT (__, on_ctype_variance1))
      (let o0 = variance_universes (E.ind_universes mdecl) _v_ in
       match o0 with
       | Some p ->
         let Coq_pair (p0, _) = p in
         let Coq_pair (u, _) = p0 in
         Obj.magic (fun _UU0393_ t0 t1 pb x ->
           h2 u _UU0393_ t0 t1 pb
             (let Coq_pair (_, x0) = coq_All_eta3 args in
              x0 (coq_All_map_inv (Obj.magic __) args x)))
       | None -> Obj.magic __ __)
      (coq_All_map (Obj.magic __) args
        (coq_All_impl args (Obj.magic hargs) (fun _ x ->
          x.on_ctype_variance _v_ __)))) }

  (** val on_constructors_impl_config_gen :
      E.global_env_ext -> E.mutual_inductive_body -> nat ->
      E.one_inductive_body -> E.context -> E.constructor_body list ->
      Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
      checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
      (((checker_flags, __) prod, __) prod, __) coq_All -> (E.context ->
      T.term -> E.typ_or_sort -> (((checker_flags, __) prod, __) prod, __)
      coq_All -> 'a2) -> (universes_decl -> E.context -> T.term -> T.term ->
      conv_pb -> (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
      (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
      on_constructors **)

  let on_constructors_impl_config_gen _UU03a3_ mdecl i idecl ind_indices0 cdecl cunivs args cf hexists hargsconfig h1 h2 hargs =
    let Coq_existT (x, y) = hexists in
    let Coq_pair (p, _) = x in
    let Coq_pair (c, _) = p in
    let Coq_pair (_, o) = Obj.magic y in
    (match args with
     | Coq_nil ->
       coq_All2_impl cdecl cunivs o (fun x0 y0 x1 ->
         on_constructor_impl_config_gen _UU03a3_ mdecl i idecl ind_indices0
           x0 y0 Coq_nil cf (Coq_existT ((Coq_pair ((Coq_pair (c, __)), __)),
           (Obj.magic (Coq_pair (__, x1))))) h1 h2 All_nil)
     | Coq_cons (p0, l) ->
       let x0 = fun ls -> let Coq_pair (x0, _) = coq_All_eta3 ls in x0 in
       let hargs0 = x0 (Coq_cons (p0, l)) hargs in
       let hargs1 = coq_All_All2_swap (Coq_cons (p0, l)) cdecl cunivs hargs0
       in
       coq_All2_impl cdecl cunivs hargs1 (fun _x_ _y_ hargs' ->
         on_constructor_impl_config_gen _UU03a3_ mdecl i idecl ind_indices0
           _x_ _y_ (Coq_cons (p0, l)) cf
           (let Coq_pair (p1, _) = p0 in
            let Coq_pair (c0, _) = p1 in
            (match hargs' with
             | All_nil -> assert false (* absurd case *)
             | All_cons (_, _, x1, _) ->
               (match hargsconfig with
                | All_nil -> assert false (* absurd case *)
                | All_cons (_, _, _, _) ->
                  Obj.magic (Coq_existT ((Coq_pair ((Coq_pair (c0, __)),
                    __)), (Coq_pair (__, x1))))))) h1 h2
           (let Coq_pair (p1, _) = p0 in
            let Coq_pair (c0, _) = p1 in
            (match hargs' with
             | All_nil -> assert false (* absurd case *)
             | All_cons (_, _, x1, x2) ->
               (match hargsconfig with
                | All_nil -> assert false (* absurd case *)
                | All_cons (_, _, _, _) ->
                  Obj.magic (All_cons ((Coq_pair ((Coq_pair (c0, __)), __)),
                    l, x1, (coq_All_impl l x2 (fun _ x3 -> x3)))))))))

  (** val ind_respects_variance_impl :
      E.global_env -> E.mutual_inductive_body -> Variance.t list -> E.context
      -> __ -> 'a1 ind_respects_variance -> 'a2 ind_respects_variance **)

  let ind_respects_variance_impl _ mdecl v cs =
    let o = variance_universes (E.ind_universes mdecl) v in
    (match o with
     | Some p ->
       (fun hPQ hP ->
         let Coq_pair (p0, l) = p in
         let Coq_pair (_, l0) = p0 in
         Obj.magic coq_All2_fold_impl
           (subst_instance E.subst_instance_context l0
             (E.expand_lets_ctx (E.ind_params mdecl)
               (E.smash_context Coq_nil cs)))
           (subst_instance E.subst_instance_context l
             (E.expand_lets_ctx (E.ind_params mdecl)
               (E.smash_context Coq_nil cs))) hP (fun _UU0393_ _ _ _ x ->
           match x with
           | C.Coq_all_decls_alpha_vass (na, na', t0, t', eqt) ->
             C.Coq_all_decls_alpha_vass (na, na', t0, t',
               (Obj.magic hPQ
                 (E.app_context
                   (subst_instance E.subst_instance_context l0
                     (E.smash_context Coq_nil (E.ind_params mdecl))) _UU0393_)
                 t0 t' Cumul eqt))
           | C.Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb, eqt) ->
             C.Coq_all_decls_alpha_vdef (na, na', b, t0, b', t',
               (Obj.magic hPQ
                 (E.app_context
                   (subst_instance E.subst_instance_context l0
                     (E.smash_context Coq_nil (E.ind_params mdecl))) _UU0393_)
                 b b' Conv eqb),
               (Obj.magic hPQ
                 (E.app_context
                   (subst_instance E.subst_instance_context l0
                     (E.smash_context Coq_nil (E.ind_params mdecl))) _UU0393_)
                 t0 t' Cumul eqt))))
     | None -> Obj.magic __)

  (** val on_variance_impl :
      E.global_env -> universes_decl -> Variance.t list option ->
      checker_flags -> checker_flags -> on_variance -> on_variance **)

  let on_variance_impl _ univs variances _ _ x =
    let _evar_0_ =
      let _evar_0_ = fun _ _ x0 ->
        let Coq_existT (x1, s) = x0 in
        let Coq_existT (x2, s0) = s in
        let Coq_existT (x3, _) = s0 in
        Coq_existT (x1, (Coq_existT (x2, (Coq_existT (x3, __)))))
      in
      let _evar_0_0 = fun _ h0 -> h0 in
      (fun cst _ x0 ->
      match variances with
      | Some a -> _evar_0_ a cst x0
      | None -> _evar_0_0 cst x0)
    in
    (match univs with
     | Monomorphic_ctx -> Obj.magic __ __ x
     | Polymorphic_ctx cst -> Obj.magic _evar_0_ cst __ x)

  (** val on_global_env_impl_config :
      checker_flags -> checker_flags -> ((E.global_env, universes_decl) prod
      -> E.context -> T.term -> E.typ_or_sort -> ('a1, 'a3) on_global_env ->
      ('a2, 'a4) on_global_env -> 'a3 -> 'a4) -> ((E.global_env,
      universes_decl) prod -> E.context -> T.term -> T.term -> conv_pb ->
      ('a1, 'a3) on_global_env -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) ->
      E.global_env -> ('a1, 'a3) on_global_env -> ('a2, 'a4) on_global_env **)

  let on_global_env_impl_config cf1 cf2 x y _UU03a3_ = function
  | Coq_pair (_, o) ->
    Coq_pair (__,
      (let univs = E.universes _UU03a3_ in
       let retro = E.retroknowledge _UU03a3_ in
       let g = E.declarations _UU03a3_ in
       let rec f l iH =
         match l with
         | Coq_nil -> Coq_globenv_nil
         | Coq_cons (y0, l0) ->
           let iH0 = (Coq_cons (y0, l0)),iH in
           let iH2 = let _,pr2 = iH0 in pr2 in
           (match iH2 with
            | Coq_globenv_nil -> assert false (* absurd case *)
            | Coq_globenv_decl (_, kn, d, o0, o1) ->
              let iHg = f l0 o0 in
              Coq_globenv_decl (l0, kn, d, iHg,
              (let udecl0 = L.universes_decl_of_decl d in
               let x' = fun _UU0393_ t0 t1 ->
                 x (Coq_pair ({ E.universes = univs; E.declarations = l0;
                   E.retroknowledge = retro }, udecl0)) _UU0393_ t0 t1
                   (Coq_pair (__, o0)) (Coq_pair (__, iHg))
               in
               let y' = fun udecl1 _UU0393_ t0 t1 pb ->
                 y (Coq_pair ({ E.universes = univs; E.declarations = l0;
                   E.retroknowledge = retro }, udecl1)) _UU0393_ t0 t1 pb
                   (Coq_pair (__, o0)) (Coq_pair (__, iHg))
               in
               (match d with
                | E.ConstantDecl c ->
                  let { E.cst_type = cst_type0; E.cst_body = cst_body0;
                    E.cst_universes = _; E.cst_relevance = _ } = c
                  in
                  (match cst_body0 with
                   | Some t0 -> Obj.magic x' Coq_nil t0 (Typ cst_type0) o1
                   | None -> Obj.magic x' Coq_nil cst_type0 Sort o1)
                | E.InductiveDecl m ->
                  let udecl1 = L.universes_decl_of_decl (E.InductiveDecl m) in
                  let { onInductives = onInductives0; onParams = onParams0;
                    onVariance = onVariance0 } = Obj.magic o1
                  in
                  Obj.magic { onInductives =
                    (coq_Alli_impl (E.ind_bodies m) O onInductives0
                      (fun n x1 x2 -> { onArity =
                      (let x3 =
                         onArity cf1 (Coq_pair ({ E.universes = univs;
                           E.declarations = l0; E.retroknowledge = retro },
                           udecl1)) kn m n x1 x2
                       in
                       x' Coq_nil (E.ind_type x1) Sort x3); ind_cunivs =
                      (ind_cunivs cf1 (Coq_pair ({ E.universes = univs;
                        E.declarations = l0; E.retroknowledge = retro },
                        udecl1)) kn m n x1 x2); onConstructors =
                      (let x11 =
                         onConstructors cf1 (Coq_pair ({ E.universes = univs;
                           E.declarations = l0; E.retroknowledge = retro },
                           udecl1)) kn m n x1 x2
                       in
                       coq_All2_impl (E.ind_ctors x1)
                         (ind_cunivs cf1 (Coq_pair ({ E.universes = univs;
                           E.declarations = l0; E.retroknowledge = retro },
                           udecl1)) kn m n x1 x2) x11 (fun x3 y1 x4 ->
                         let { on_ctype = on_ctype0; on_cargs = on_cargs0;
                           on_cindices = on_cindices0; on_ctype_positive =
                           on_ctype_positive0; on_ctype_variance =
                           on_ctype_variance0 } = x4
                         in
                         { on_ctype =
                         (x' (E.arities_context (E.ind_bodies m))
                           (E.cstr_type x3) Sort on_ctype0); on_cargs =
                         (let c = E.cstr_args x3 in
                          let rec f0 l1 y2 =
                            match l1 with
                            | Coq_nil ->
                              (match y2 with
                               | Coq_nil -> (fun on_cargs1 -> on_cargs1)
                               | Coq_cons (x5, x6) -> Obj.magic __ x5 x6)
                            | Coq_cons (y3, l2) ->
                              (match y2 with
                               | Coq_nil ->
                                 let { decl_name = _; decl_body = decl_body0;
                                   decl_type = decl_type0 } = y3
                                 in
                                 (match decl_body0 with
                                  | Some t0 ->
                                    (fun on_cargs1 ->
                                      Obj.magic (Coq_pair
                                        ((let Coq_pair (a, _) =
                                            Obj.magic on_cargs1
                                          in
                                          f0 l2 Coq_nil a),
                                        (let Coq_pair (_, b) =
                                           Obj.magic on_cargs1
                                         in
                                         let Coq_pair (a, b0) = b in
                                         Coq_pair
                                         ((x'
                                            (E.app_context
                                              (E.app_context
                                                (E.arities_context
                                                  (E.ind_bodies m))
                                                (E.ind_params m)) l2)
                                            decl_type0 Sort a),
                                         (x'
                                           (E.app_context
                                             (E.app_context
                                               (E.arities_context
                                                 (E.ind_bodies m))
                                               (E.ind_params m)) l2) t0 (Typ
                                           decl_type0) b0))))))
                                  | None -> Obj.magic __ decl_type0)
                               | Coq_cons (t0, l3) ->
                                 (fun on_cargs1 ->
                                   let { decl_name = _; decl_body =
                                     decl_body0; decl_type = decl_type0 } = y3
                                   in
                                   (match decl_body0 with
                                    | Some t1 ->
                                      Obj.magic (Coq_pair
                                        ((let Coq_pair (a, _) =
                                            Obj.magic on_cargs1
                                          in
                                          f0 l2 (Coq_cons (t0, l3)) a),
                                        (let Coq_pair (_, b) =
                                           Obj.magic on_cargs1
                                         in
                                         let Coq_pair (a, b0) = b in
                                         Coq_pair
                                         ((x'
                                            (E.app_context
                                              (E.app_context
                                                (E.arities_context
                                                  (E.ind_bodies m))
                                                (E.ind_params m)) l2)
                                            decl_type0 Sort a),
                                         (x'
                                           (E.app_context
                                             (E.app_context
                                               (E.arities_context
                                                 (E.ind_bodies m))
                                               (E.ind_params m)) l2) t1 (Typ
                                           decl_type0) b0)))))
                                    | None ->
                                      Obj.magic (Coq_pair
                                        ((let Coq_pair (a, _) =
                                            Obj.magic on_cargs1
                                          in
                                          f0 l2 l3 a),
                                        (let Coq_pair (_, b) =
                                           Obj.magic on_cargs1
                                         in
                                         x'
                                           (E.app_context
                                             (E.app_context
                                               (E.arities_context
                                                 (E.ind_bodies m))
                                               (E.ind_params m)) l2)
                                           decl_type0 (Typ (T.tSort t0)) b))))))
                          in f0 c y1 on_cargs0); on_cindices =
                         (let l1 = E.cstr_indices x3 in
                          let l2 =
                            List.rev
                              (E.lift_context (length (E.cstr_args x3)) O
                                (E.ind_indices x1))
                          in
                          ET.ctx_inst_rect (Coq_pair ({ E.universes = univs;
                            E.declarations = l0; E.retroknowledge = retro },
                            udecl1))
                            (E.app_context
                              (E.app_context
                                (E.arities_context (E.ind_bodies m))
                                (E.ind_params m)) (E.cstr_args x3))
                            ET.Coq_ctx_inst_nil
                            (fun na t0 i inst _UU0394_ t1 _ iHon_cindices0 ->
                            ET.Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_,
                            (x'
                              (E.app_context
                                (E.app_context
                                  (E.arities_context (E.ind_bodies m))
                                  (E.ind_params m)) (E.cstr_args x3)) i (Typ
                              t0) t1), iHon_cindices0))
                            (fun na b t0 inst _UU0394_ _ iHon_cindices0 ->
                            ET.Coq_ctx_inst_def (na, b, t0, inst, _UU0394_,
                            iHon_cindices0)) l1 l2 on_cindices0);
                         on_ctype_positive = on_ctype_positive0;
                         on_ctype_variance = (fun v _ ->
                         cstr_respects_variance_impl
                           (E.fst_ctx (Coq_pair ({ E.universes = univs;
                             E.declarations = l0; E.retroknowledge = retro },
                             (E.ind_universes m)))) m v x3
                           (let o2 = variance_universes (E.ind_universes m) v
                            in
                            match o2 with
                            | Some p ->
                              let Coq_pair (p0, _) = p in
                              let Coq_pair (u, _) = p0 in
                              Obj.magic (fun _UU0393_ t0 t1 pb x5 ->
                                y' u _UU0393_ t0 t1 pb x5)
                            | None -> Obj.magic __ __)
                           (on_ctype_variance0 v __)) })); onProjections =
                      (onProjections cf1 (Coq_pair ({ E.universes = univs;
                        E.declarations = l0; E.retroknowledge = retro },
                        udecl1)) kn m n x1 x2); ind_sorts =
                      (let { onArity = _; ind_cunivs = _; onConstructors = _;
                         onProjections = _; ind_sorts = ind_sorts0;
                         onIndices = _ } = x2
                       in
                       let b = Universe.is_prop (E.ind_sort x1) in
                       (match b with
                        | Coq_true -> Obj.magic __ ind_sorts0
                        | Coq_false ->
                          let b0 = Universe.is_sprop (E.ind_sort x1) in
                          (match b0 with
                           | Coq_true -> Obj.magic __ ind_sorts0
                           | Coq_false ->
                             Obj.magic (Coq_pair (__,
                               (let Coq_pair (_, y1) = Obj.magic ind_sorts0 in
                                let b1 = cf1.indices_matter in
                                (match b1 with
                                 | Coq_true ->
                                   let b2 = cf2.indices_matter in
                                   (match b2 with
                                    | Coq_true ->
                                      type_local_ctx_impl (Coq_pair
                                        ({ E.universes = univs;
                                        E.declarations = l0;
                                        E.retroknowledge = retro },
                                        (E.ind_universes m)))
                                        (E.ind_params m) (E.ind_indices x1)
                                        (E.ind_sort x1) y1 x'
                                    | Coq_false -> Obj.magic __ __)
                                 | Coq_false ->
                                   let b2 = cf2.indices_matter in
                                   (match b2 with
                                    | Coq_true ->
                                      assert false (* absurd case *)
                                    | Coq_false -> Obj.magic __ __))))))));
                      onIndices =
                      (let o2 = E.ind_variance m in
                       match o2 with
                       | Some l1 ->
                         ind_respects_variance_impl
                           (E.fst_ctx (Coq_pair ({ E.universes = univs;
                             E.declarations = l0; E.retroknowledge = retro },
                             (E.ind_universes m)))) m l1 (E.ind_indices x1)
                           (let o3 = variance_universes (E.ind_universes m) l1
                            in
                            match o3 with
                            | Some p ->
                              let Coq_pair (p0, _) = p in
                              let Coq_pair (u, _) = p0 in
                              Obj.magic (fun _UU0393_ t0 t1 pb x3 ->
                                y' u _UU0393_ t0 t1 pb x3)
                            | None -> Obj.magic __ __)
                           (onIndices cf1 (Coq_pair ({ E.universes = univs;
                             E.declarations = l0; E.retroknowledge = retro },
                             udecl1)) kn m n x1 x2)
                       | None ->
                         Obj.magic __ __ onVariance0
                           (onIndices cf1 (Coq_pair ({ E.universes = univs;
                             E.declarations = l0; E.retroknowledge = retro },
                             udecl1)) kn m n x1 x2)) })); onParams =
                    (ET.coq_All_local_env_impl (E.ind_params m) onParams0 x');
                    onVariance =
                    (on_variance_impl
                      (E.fst_ctx (Coq_pair ({ E.universes = univs;
                        E.declarations = l0; E.retroknowledge = retro },
                        (E.ind_universes m)))) (E.ind_universes m)
                      (E.ind_variance m) cf1 cf2 onVariance0) }))))
       in f g o))

  (** val on_global_env_impl :
      checker_flags -> ((E.global_env, universes_decl) prod -> E.context ->
      T.term -> E.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
      on_global_env -> 'a2 -> 'a3) -> E.global_env -> ('a1, 'a2)
      on_global_env -> ('a1, 'a3) on_global_env **)

  let on_global_env_impl cf x _UU03a3_ x0 =
    on_global_env_impl_config cf cf x (fun _ _ _ _ _ _ _ x3 -> x3) _UU03a3_ x0
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

module DeclarationTyping =
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
 struct
  type isType = Ty.typing ET.infer_sort

  type 'p coq_Forall_decls_typing =
    (CS.cumul_gen, 'p ET.lift_typing) GM.on_global_env

  type type_local_decl = __

  (** val refine_type :
      checker_flags -> E.global_env_ext -> E.context -> T.term -> T.term ->
      T.term -> Ty.typing -> Ty.typing **)

  let refine_type _ _ _ _ _ _ ht =
    ht

  type wf_local_rel = Ty.typing ET.lift_typing ET.coq_All_local_rel

  (** val on_wf_global_env_impl_config :
      checker_flags -> checker_flags -> checker_flags -> E.global_env ->
      (CS.cumul_gen, Ty.typing ET.lift_typing) GM.on_global_env ->
      (E.global_env_ext -> E.context -> conv_pb -> T.term -> T.term ->
      CS.cumul_gen -> CS.cumul_gen) -> ((E.global_env, universes_decl) prod
      -> E.context -> T.term -> E.typ_or_sort -> (CS.cumul_gen, Ty.typing
      ET.lift_typing) GM.on_global_env -> (CS.cumul_gen, 'a1)
      GM.on_global_env -> (CS.cumul_gen, 'a2) GM.on_global_env -> 'a1 -> 'a2)
      -> (CS.cumul_gen, 'a1) GM.on_global_env -> (CS.cumul_gen, 'a2)
      GM.on_global_env **)

  let on_wf_global_env_impl_config _ cf2 cf3 _UU03a3_ wf_UU03a3_ hcumul x = function
  | Coq_pair (_, o) ->
    Coq_pair (__,
      (let Coq_pair (_, o0) = wf_UU03a3_ in
       let univs = E.universes _UU03a3_ in
       let retro = E.retroknowledge _UU03a3_ in
       let g = E.declarations _UU03a3_ in
       GM.on_global_decls_rect cf2 univs retro (fun _ _ ->
         GM.Coq_globenv_nil) (fun _UU03a3_0 kn d x0 iHX0 o1 _ wf_UU03a3_0 ->
         GM.Coq_globenv_decl (_UU03a3_0, kn, d,
         (let wf_UU03a3_1 = (snoc _UU03a3_0 (Coq_pair (kn, d))),wf_UU03a3_0 in
          let wf_UU03a3_2 = let _,pr2 = wf_UU03a3_1 in pr2 in
          (match wf_UU03a3_2 with
           | GM.Coq_globenv_nil -> assert false (* absurd case *)
           | GM.Coq_globenv_decl (_, _, _, o2, _) -> iHX0 __ o2)),
         (let udecl0 = L.universes_decl_of_decl d in
          let wf_UU03a3_1 = (snoc _UU03a3_0 (Coq_pair (kn, d))),wf_UU03a3_0 in
          let wf_UU03a3_2 = let _,pr2 = wf_UU03a3_1 in pr2 in
          (match wf_UU03a3_2 with
           | GM.Coq_globenv_nil -> assert false (* absurd case *)
           | GM.Coq_globenv_decl (_, _, _, o2, _) ->
             let iHX1 = iHX0 __ o2 in
             let x' = fun _UU0393_ t0 t1 ->
               x (Coq_pair ({ E.universes = univs; E.declarations =
                 _UU03a3_0; E.retroknowledge = retro }, udecl0)) _UU0393_ t0
                 t1 (Coq_pair (__, o2)) (Coq_pair (__, x0)) (Coq_pair (__,
                 iHX1))
             in
             (match d with
              | E.ConstantDecl c ->
                let { E.cst_type = cst_type0; E.cst_body = cst_body0;
                  E.cst_universes = cst_universes0; E.cst_relevance =
                  cst_relevance0 } = c
                in
                (match cst_body0 with
                 | Some t0 ->
                   Obj.magic x' Coq_nil t0 (Typ
                     (E.cst_type { E.cst_type = cst_type0; E.cst_body = (Some
                       t0); E.cst_universes = cst_universes0;
                       E.cst_relevance = cst_relevance0 })) o1
                 | None ->
                   Obj.magic x' Coq_nil
                     (E.cst_type { E.cst_type = cst_type0; E.cst_body = None;
                       E.cst_universes = cst_universes0; E.cst_relevance =
                       cst_relevance0 }) Sort o1)
              | E.InductiveDecl m ->
                let udecl1 = L.universes_decl_of_decl (E.InductiveDecl m) in
                let { GM.onInductives = onInductives0; GM.onParams =
                  onParams0; GM.onVariance = onVariance0 } = Obj.magic o1
                in
                Obj.magic { GM.onInductives =
                  (coq_Alli_impl (E.ind_bodies m) O onInductives0
                    (fun n x2 x3 -> { GM.onArity =
                    (let x4 =
                       GM.onArity cf2 (Coq_pair ({ E.universes = univs;
                         E.declarations = _UU03a3_0; E.retroknowledge =
                         retro }, udecl1)) kn m n x2 x3
                     in
                     x' Coq_nil (E.ind_type x2) Sort x4); GM.ind_cunivs =
                    (GM.ind_cunivs cf2 (Coq_pair ({ E.universes = univs;
                      E.declarations = _UU03a3_0; E.retroknowledge = retro },
                      udecl1)) kn m n x2 x3); GM.onConstructors =
                    (let x11 =
                       GM.onConstructors cf2 (Coq_pair ({ E.universes =
                         univs; E.declarations = _UU03a3_0;
                         E.retroknowledge = retro }, udecl1)) kn m n x2 x3
                     in
                     coq_All2_impl (E.ind_ctors x2)
                       (GM.ind_cunivs cf2 (Coq_pair ({ E.universes = univs;
                         E.declarations = _UU03a3_0; E.retroknowledge =
                         retro }, udecl1)) kn m n x2 x3) x11 (fun x4 y x5 ->
                       let { GM.on_ctype = on_ctype0; GM.on_cargs =
                         on_cargs0; GM.on_cindices = on_cindices0;
                         GM.on_ctype_positive = on_ctype_positive0;
                         GM.on_ctype_variance = on_ctype_variance0 } = x5
                       in
                       { GM.on_ctype =
                       (x' (E.arities_context (E.ind_bodies m))
                         (E.cstr_type x4) Sort on_ctype0); GM.on_cargs =
                       (let c = E.cstr_args x4 in
                        let rec f l y0 =
                          match l with
                          | Coq_nil ->
                            (match y0 with
                             | Coq_nil -> (fun on_cargs1 -> on_cargs1)
                             | Coq_cons (x6, x7) -> Obj.magic __ x6 x7)
                          | Coq_cons (y1, l0) ->
                            (match y0 with
                             | Coq_nil ->
                               let { decl_name = _; decl_body = decl_body0;
                                 decl_type = decl_type0 } = y1
                               in
                               (match decl_body0 with
                                | Some t0 ->
                                  (fun on_cargs1 ->
                                    Obj.magic (Coq_pair
                                      ((let Coq_pair (a, _) =
                                          Obj.magic on_cargs1
                                        in
                                        f l0 Coq_nil a),
                                      (let Coq_pair (_, b) =
                                         Obj.magic on_cargs1
                                       in
                                       let Coq_pair (a, b0) = b in
                                       Coq_pair
                                       ((x'
                                          (E.app_context
                                            (E.app_context
                                              (E.arities_context
                                                (E.ind_bodies m))
                                              (E.ind_params m)) l0)
                                          decl_type0 Sort a),
                                       (x'
                                         (E.app_context
                                           (E.app_context
                                             (E.arities_context
                                               (E.ind_bodies m))
                                             (E.ind_params m)) l0) t0 (Typ
                                         decl_type0) b0))))))
                                | None -> Obj.magic __ decl_type0)
                             | Coq_cons (t0, l1) ->
                               (fun on_cargs1 ->
                                 let { decl_name = _; decl_body = decl_body0;
                                   decl_type = decl_type0 } = y1
                                 in
                                 (match decl_body0 with
                                  | Some t1 ->
                                    Obj.magic (Coq_pair
                                      ((let Coq_pair (a, _) =
                                          Obj.magic on_cargs1
                                        in
                                        f l0 (Coq_cons (t0, l1)) a),
                                      (let Coq_pair (_, b) =
                                         Obj.magic on_cargs1
                                       in
                                       let Coq_pair (a, b0) = b in
                                       Coq_pair
                                       ((x'
                                          (E.app_context
                                            (E.app_context
                                              (E.arities_context
                                                (E.ind_bodies m))
                                              (E.ind_params m)) l0)
                                          decl_type0 Sort a),
                                       (x'
                                         (E.app_context
                                           (E.app_context
                                             (E.arities_context
                                               (E.ind_bodies m))
                                             (E.ind_params m)) l0) t1 (Typ
                                         decl_type0) b0)))))
                                  | None ->
                                    Obj.magic (Coq_pair
                                      ((let Coq_pair (a, _) =
                                          Obj.magic on_cargs1
                                        in
                                        f l0 l1 a),
                                      (let Coq_pair (_, b) =
                                         Obj.magic on_cargs1
                                       in
                                       x'
                                         (E.app_context
                                           (E.app_context
                                             (E.arities_context
                                               (E.ind_bodies m))
                                             (E.ind_params m)) l0) decl_type0
                                         (Typ (T.tSort t0)) b))))))
                        in f c y on_cargs0); GM.on_cindices =
                       (let l = E.cstr_indices x4 in
                        let l0 =
                          List.rev
                            (E.lift_context (length (E.cstr_args x4)) O
                              (E.ind_indices x2))
                        in
                        ET.ctx_inst_rect (Coq_pair ({ E.universes = univs;
                          E.declarations = _UU03a3_0; E.retroknowledge =
                          retro }, udecl1))
                          (E.app_context
                            (E.app_context
                              (E.arities_context (E.ind_bodies m))
                              (E.ind_params m)) (E.cstr_args x4))
                          ET.Coq_ctx_inst_nil
                          (fun na t0 i inst _UU0394_ t1 _ iHon_cindices0 ->
                          ET.Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_,
                          (x'
                            (E.app_context
                              (E.app_context
                                (E.arities_context (E.ind_bodies m))
                                (E.ind_params m)) (E.cstr_args x4)) i (Typ
                            t0) t1), iHon_cindices0))
                          (fun na b t0 inst _UU0394_ _ iHon_cindices0 ->
                          ET.Coq_ctx_inst_def (na, b, t0, inst, _UU0394_,
                          iHon_cindices0)) l l0 on_cindices0);
                       GM.on_ctype_positive = on_ctype_positive0;
                       GM.on_ctype_variance = (fun v _ ->
                       let o3 = GM.variance_universes (E.ind_universes m) v in
                       (match o3 with
                        | Some p ->
                          let __top_assumption_ = on_ctype_variance0 v __ in
                          let Coq_pair (p0, l) = p in
                          let Coq_pair (u, l0) = p0 in
                          let _evar_0_ = fun h1 h2 -> Coq_pair
                            ((coq_All2_fold_impl
                               (subst_instance E.subst_instance_context l0
                                 (E.expand_lets_ctx (E.ind_params m)
                                   (E.smash_context Coq_nil (E.cstr_args x4))))
                               (subst_instance E.subst_instance_context l
                                 (E.expand_lets_ctx (E.ind_params m)
                                   (E.smash_context Coq_nil (E.cstr_args x4))))
                               h1 (fun _UU0393_ _ d0 d' ->
                               CT.coq_All_decls_alpha_pb_impl Cumul d0 d'
                                 (fun pb t0 t' x6 ->
                                 hcumul (Coq_pair ({ E.universes = univs;
                                   E.declarations = _UU03a3_0;
                                   E.retroknowledge = retro }, u))
                                   (E.app_context
                                     (subst_instance E.subst_instance_context
                                       l0
                                       (E.app_context (GM.ind_arities m)
                                         (E.smash_context Coq_nil
                                           (E.ind_params m)))) _UU0393_) pb
                                   t0 t' x6))),
                            (coq_All2_impl
                              (map (fun x6 ->
                                subst_instance T.subst_instance_constr l0
                                  (E.expand_lets
                                    (E.app_context (E.ind_params m)
                                      (E.cstr_args x4)) x6))
                                (E.cstr_indices x4))
                              (map (fun x6 ->
                                subst_instance T.subst_instance_constr l
                                  (E.expand_lets
                                    (E.app_context (E.ind_params m)
                                      (E.cstr_args x4)) x6))
                                (E.cstr_indices x4)) h2 (fun x6 y0 x7 ->
                              hcumul (Coq_pair ({ E.universes = univs;
                                E.declarations = _UU03a3_0;
                                E.retroknowledge = retro }, u))
                                (subst_instance E.subst_instance_context l0
                                  (E.app_context (GM.ind_arities m)
                                    (E.smash_context Coq_nil
                                      (E.app_context (E.ind_params m)
                                        (E.cstr_args x4))))) Conv x6 y0 x7)))
                          in
                          let Coq_pair (a, b) = Obj.magic __top_assumption_ in
                          Obj.magic _evar_0_ a b
                        | None -> Obj.magic __ __ __ (on_ctype_variance0 v __))) }));
                    GM.onProjections =
                    (GM.onProjections cf2 (Coq_pair ({ E.universes = univs;
                      E.declarations = _UU03a3_0; E.retroknowledge = retro },
                      udecl1)) kn m n x2 x3); GM.ind_sorts =
                    (let { GM.onArity = _; GM.ind_cunivs = _;
                       GM.onConstructors = _; GM.onProjections = _;
                       GM.ind_sorts = ind_sorts0; GM.onIndices = _ } = x3
                     in
                     let b = Universe.is_prop (E.ind_sort x2) in
                     (match b with
                      | Coq_true -> Obj.magic __ ind_sorts0
                      | Coq_false ->
                        let b0 = Universe.is_sprop (E.ind_sort x2) in
                        (match b0 with
                         | Coq_true -> Obj.magic __ ind_sorts0
                         | Coq_false ->
                           Obj.magic (Coq_pair (__,
                             (let Coq_pair (_, y) = Obj.magic ind_sorts0 in
                              let b1 = cf2.indices_matter in
                              (match b1 with
                               | Coq_true ->
                                 let b2 = cf3.indices_matter in
                                 (match b2 with
                                  | Coq_true ->
                                    GM.type_local_ctx_impl (Coq_pair
                                      ({ E.universes = univs;
                                      E.declarations = _UU03a3_0;
                                      E.retroknowledge = retro },
                                      (E.ind_universes m))) (E.ind_params m)
                                      (E.ind_indices x2) (E.ind_sort x2) y x'
                                  | Coq_false -> Obj.magic __ __)
                               | Coq_false ->
                                 let b2 = cf3.indices_matter in
                                 (match b2 with
                                  | Coq_true -> assert false (* absurd case *)
                                  | Coq_false -> Obj.magic __ __))))))));
                    GM.onIndices =
                    (let o3 = E.ind_variance m in
                     match o3 with
                     | Some l ->
                       GM.ind_respects_variance_impl
                         (E.fst_ctx (Coq_pair ({ E.universes = univs;
                           E.declarations = _UU03a3_0; E.retroknowledge =
                           retro }, (E.ind_universes m)))) m l
                         (E.ind_indices x2)
                         (let o4 = GM.variance_universes (E.ind_universes m) l
                          in
                          match o4 with
                          | Some p ->
                            let Coq_pair (p0, _) = p in
                            let Coq_pair (u, _) = p0 in
                            Obj.magic (fun _UU0393_ t0 t1 pb x4 ->
                              hcumul (Coq_pair
                                ((E.fst_ctx (Coq_pair ({ E.universes = univs;
                                   E.declarations = _UU03a3_0;
                                   E.retroknowledge = retro },
                                   (E.ind_universes m)))), u)) _UU0393_ pb t0
                                t1 x4)
                          | None -> Obj.magic __ __)
                         (GM.onIndices cf2 (Coq_pair ({ E.universes = univs;
                           E.declarations = _UU03a3_0; E.retroknowledge =
                           retro }, udecl1)) kn m n x2 x3)
                     | None ->
                       Obj.magic __ __ onVariance0
                         (GM.onIndices cf2 (Coq_pair ({ E.universes = univs;
                           E.declarations = _UU03a3_0; E.retroknowledge =
                           retro }, udecl1)) kn m n x2 x3)) }));
                  GM.onParams =
                  (ET.coq_All_local_env_impl (E.ind_params m) onParams0 x');
                  GM.onVariance =
                  (GM.on_variance_impl
                    (E.fst_ctx (Coq_pair ({ E.universes = univs;
                      E.declarations = _UU03a3_0; E.retroknowledge = retro },
                      (E.ind_universes m)))) (E.ind_universes m)
                    (E.ind_variance m) cf2 cf3 onVariance0) }))))) g o __ o0))

  (** val on_wf_global_env_impl :
      checker_flags -> E.global_env -> (CS.cumul_gen, Ty.typing
      ET.lift_typing) GM.on_global_env -> ((E.global_env, universes_decl)
      prod -> E.context -> T.term -> E.typ_or_sort -> (CS.cumul_gen,
      Ty.typing ET.lift_typing) GM.on_global_env -> (CS.cumul_gen, 'a1)
      GM.on_global_env -> (CS.cumul_gen, 'a2) GM.on_global_env -> 'a1 -> 'a2)
      -> (CS.cumul_gen, 'a1) GM.on_global_env -> (CS.cumul_gen, 'a2)
      GM.on_global_env **)

  let on_wf_global_env_impl h _UU03a3_ wf_UU03a3_ =
    on_wf_global_env_impl_config h h h _UU03a3_ wf_UU03a3_
      (fun _ _ _ _ _ x -> x)
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
