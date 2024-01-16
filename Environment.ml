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
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

module TermDecideReflectInstances =
 functor (T:Term) ->
 functor (TDec:sig
  val term_eq_dec : T.term coq_EqDec
 end) ->
 struct
 end

module Retroknowledge =
 struct
  type t = { retro_int63 : kername option; retro_float64 : kername option }

  (** val retro_int63 : t -> kername option **)

  let retro_int63 t0 =
    t0.retro_int63

  (** val retro_float64 : t -> kername option **)

  let retro_float64 t0 =
    t0.retro_float64

  (** val empty : t **)

  let empty =
    { retro_int63 = None; retro_float64 = None }

  (** val extendsb : t -> t -> bool **)

  let extendsb x y =
    match option_extendsb Kername.reflect_kername x.retro_int63 y.retro_int63 with
    | Coq_true ->
      option_extendsb Kername.reflect_kername x.retro_float64 y.retro_float64
    | Coq_false -> Coq_false

  (** val extendsT : t -> t -> reflect **)

  let extendsT x y =
    let _evar_0_ =
      let _evar_0_ = fun _ _ -> ReflectT in
      let _evar_0_0 = fun _ _ -> ReflectF in
      (match option_extendsT Kername.reflect_kername x.retro_float64
               y.retro_float64 with
       | ReflectT -> _evar_0_ __
       | ReflectF -> _evar_0_0 __)
    in
    let _evar_0_0 =
      let _evar_0_0 = fun _ _ -> ReflectF in
      let _evar_0_1 = fun _ _ -> ReflectF in
      (match option_extendsT Kername.reflect_kername x.retro_float64
               y.retro_float64 with
       | ReflectT -> _evar_0_0 __
       | ReflectF -> _evar_0_1 __)
    in
    (match option_extendsT Kername.reflect_kername x.retro_int63 y.retro_int63 with
     | ReflectT -> _evar_0_ __
     | ReflectF -> _evar_0_0 __)

  (** val reflect_t : t coq_ReflectEq **)

  let reflect_t x y =
    match eqb (reflect_option Kername.reflect_kername) x.retro_int63
            y.retro_int63 with
    | Coq_true ->
      eqb (reflect_option Kername.reflect_kername) x.retro_float64
        y.retro_float64
    | Coq_false -> Coq_false

  (** val merge : t -> t -> t **)

  let merge r1 r2 =
    { retro_int63 =
      (match r1.retro_int63 with
       | Some v -> Some v
       | None -> r2.retro_int63); retro_float64 =
      (match r1.retro_float64 with
       | Some v -> Some v
       | None -> r2.retro_float64) }

  (** val compatible : t -> t -> bool **)

  let compatible x y =
    match match x.retro_int63 with
          | Some x0 ->
            (match y.retro_int63 with
             | Some y0 -> eqb Kername.reflect_kername x0 y0
             | None -> Coq_true)
          | None -> Coq_true with
    | Coq_true ->
      (match x.retro_float64 with
       | Some x0 ->
         (match y.retro_float64 with
          | Some y0 -> eqb Kername.reflect_kername x0 y0
          | None -> Coq_true)
       | None -> Coq_true)
    | Coq_false -> Coq_false
 end

module Environment =
 functor (T:Term) ->
 struct
  type typ_or_sort = T.term typ_or_sort_

  (** val vass : aname -> T.term -> T.term context_decl **)

  let vass x a =
    { decl_name = x; decl_body = None; decl_type = a }

  (** val vdef : aname -> T.term -> T.term -> T.term context_decl **)

  let vdef x t0 a =
    { decl_name = x; decl_body = (Some t0); decl_type = a }

  type context = T.term context_decl list

  (** val lift_decl :
      nat -> nat -> T.term context_decl -> T.term context_decl **)

  let lift_decl n k d =
    map_decl (T.lift n k) d

  (** val lift_context : nat -> nat -> context -> context **)

  let lift_context n k _UU0393_ =
    fold_context_k (fun k' -> T.lift n (add k' k)) _UU0393_

  (** val subst_context : T.term list -> nat -> context -> context **)

  let subst_context s k _UU0393_ =
    fold_context_k (fun k' -> T.subst s (add k' k)) _UU0393_

  (** val subst_decl :
      T.term list -> nat -> T.term context_decl -> T.term context_decl **)

  let subst_decl s k d =
    map_decl (T.subst s k) d

  (** val subst_telescope : T.term list -> nat -> context -> context **)

  let subst_telescope s k _UU0393_ =
    mapi (fun k' decl -> map_decl (T.subst s (add k' k)) decl) _UU0393_

  (** val subst_instance_decl : T.term context_decl coq_UnivSubst **)

  let subst_instance_decl =
    let f0 = subst_instance T.subst_instance_constr in
    (fun x -> map_decl (f0 x))

  (** val subst_instance_context : context coq_UnivSubst **)

  let subst_instance_context =
    let f0 = subst_instance T.subst_instance_constr in
    (fun x -> map_context (f0 x))

  (** val set_binder_name :
      aname -> T.term context_decl -> T.term context_decl **)

  let set_binder_name na x =
    { decl_name = na; decl_body = x.decl_body; decl_type = x.decl_type }

  (** val context_assumptions : context -> nat **)

  let rec context_assumptions = function
  | Coq_nil -> O
  | Coq_cons (d, _UU0393_0) ->
    (match d.decl_body with
     | Some _ -> context_assumptions _UU0393_0
     | None -> S (context_assumptions _UU0393_0))

  (** val is_assumption_context : context -> bool **)

  let rec is_assumption_context = function
  | Coq_nil -> Coq_true
  | Coq_cons (d, _UU0393_0) ->
    (match d.decl_body with
     | Some _ -> Coq_false
     | None -> is_assumption_context _UU0393_0)

  (** val smash_context : context -> context -> context **)

  let rec smash_context _UU0393_ = function
  | Coq_nil -> _UU0393_
  | Coq_cons (d, _UU0393_'0) ->
    let { decl_name = _; decl_body = decl_body0; decl_type = _ } = d in
    (match decl_body0 with
     | Some b ->
       smash_context (subst_context (Coq_cons (b, Coq_nil)) O _UU0393_)
         _UU0393_'0
     | None -> smash_context (app _UU0393_ (Coq_cons (d, Coq_nil))) _UU0393_'0)

  (** val extended_subst : context -> nat -> T.term list **)

  let rec extended_subst _UU0393_ n =
    match _UU0393_ with
    | Coq_nil -> Coq_nil
    | Coq_cons (d, vs) ->
      (match d.decl_body with
       | Some b ->
         let s = extended_subst vs n in
         let b' = T.lift (add (context_assumptions vs) n) (length s) b in
         let b'0 = T.subst s O b' in Coq_cons (b'0, s)
       | None -> Coq_cons ((T.tRel n), (extended_subst vs (S n))))

  (** val expand_lets_k : context -> nat -> T.term -> T.term **)

  let expand_lets_k _UU0393_ k t0 =
    T.subst (extended_subst _UU0393_ O) k
      (T.lift (context_assumptions _UU0393_) (add k (length _UU0393_)) t0)

  (** val expand_lets : context -> T.term -> T.term **)

  let expand_lets _UU0393_ t0 =
    expand_lets_k _UU0393_ O t0

  (** val expand_lets_k_ctx : context -> nat -> context -> context **)

  let expand_lets_k_ctx _UU0393_ k _UU0394_ =
    subst_context (extended_subst _UU0393_ O) k
      (lift_context (context_assumptions _UU0393_) (add k (length _UU0393_))
        _UU0394_)

  (** val expand_lets_ctx : context -> context -> context **)

  let expand_lets_ctx _UU0393_ _UU0394_ =
    expand_lets_k_ctx _UU0393_ O _UU0394_

  (** val fix_context : T.term mfixpoint -> context **)

  let fix_context m =
    List.rev (mapi (fun i d -> vass d.dname (T.lift i O d.dtype)) m)

  type constructor_body = { cstr_name : ident; cstr_args : context;
                            cstr_indices : T.term list; cstr_type : T.term;
                            cstr_arity : nat }

  (** val cstr_name : constructor_body -> ident **)

  let cstr_name c =
    c.cstr_name

  (** val cstr_args : constructor_body -> context **)

  let cstr_args c =
    c.cstr_args

  (** val cstr_indices : constructor_body -> T.term list **)

  let cstr_indices c =
    c.cstr_indices

  (** val cstr_type : constructor_body -> T.term **)

  let cstr_type c =
    c.cstr_type

  (** val cstr_arity : constructor_body -> nat **)

  let cstr_arity c =
    c.cstr_arity

  type projection_body = { proj_name : ident; proj_relevance : relevance;
                           proj_type : T.term }

  (** val proj_name : projection_body -> ident **)

  let proj_name p =
    p.proj_name

  (** val proj_relevance : projection_body -> relevance **)

  let proj_relevance p =
    p.proj_relevance

  (** val proj_type : projection_body -> T.term **)

  let proj_type p =
    p.proj_type

  (** val map_constructor_body :
      nat -> nat -> (nat -> T.term -> T.term) -> constructor_body ->
      constructor_body **)

  let map_constructor_body npars arities f c =
    { cstr_name = (cstr_name c); cstr_args =
      (fold_context_k (fun x -> f (add (add x npars) arities)) (cstr_args c));
      cstr_indices =
      (map (f (add (add npars arities) (length (cstr_args c))))
        (cstr_indices c)); cstr_type = (f arities (cstr_type c));
      cstr_arity = (cstr_arity c) }

  (** val map_projection_body :
      nat -> (nat -> T.term -> T.term) -> projection_body -> projection_body **)

  let map_projection_body npars f c =
    { proj_name = (proj_name c); proj_relevance = (proj_relevance c);
      proj_type = (f (S npars) (proj_type c)) }

  type one_inductive_body = { ind_name : ident; ind_indices : context;
                              ind_sort : Universe.t; ind_type : T.term;
                              ind_kelim : allowed_eliminations;
                              ind_ctors : constructor_body list;
                              ind_projs : projection_body list;
                              ind_relevance : relevance }

  (** val ind_name : one_inductive_body -> ident **)

  let ind_name o =
    o.ind_name

  (** val ind_indices : one_inductive_body -> context **)

  let ind_indices o =
    o.ind_indices

  (** val ind_sort : one_inductive_body -> Universe.t **)

  let ind_sort o =
    o.ind_sort

  (** val ind_type : one_inductive_body -> T.term **)

  let ind_type o =
    o.ind_type

  (** val ind_kelim : one_inductive_body -> allowed_eliminations **)

  let ind_kelim o =
    o.ind_kelim

  (** val ind_ctors : one_inductive_body -> constructor_body list **)

  let ind_ctors o =
    o.ind_ctors

  (** val ind_projs : one_inductive_body -> projection_body list **)

  let ind_projs o =
    o.ind_projs

  (** val ind_relevance : one_inductive_body -> relevance **)

  let ind_relevance o =
    o.ind_relevance

  (** val map_one_inductive_body :
      nat -> nat -> (nat -> T.term -> T.term) -> one_inductive_body ->
      one_inductive_body **)

  let map_one_inductive_body npars arities f m =
    let { ind_name = ind_name0; ind_indices = ind_indices0; ind_sort =
      ind_sort0; ind_type = ind_type0; ind_kelim = ind_kelim0; ind_ctors =
      ind_ctors0; ind_projs = ind_projs0; ind_relevance = ind_relevance0 } = m
    in
    { ind_name = ind_name0; ind_indices =
    (fold_context_k (fun x -> f (add npars x)) ind_indices0); ind_sort =
    ind_sort0; ind_type = (f O ind_type0); ind_kelim = ind_kelim0;
    ind_ctors = (map (map_constructor_body npars arities f) ind_ctors0);
    ind_projs = (map (map_projection_body npars f) ind_projs0);
    ind_relevance = ind_relevance0 }

  type mutual_inductive_body = { ind_finite : recursivity_kind;
                                 ind_npars : nat; ind_params : context;
                                 ind_bodies : one_inductive_body list;
                                 ind_universes : universes_decl;
                                 ind_variance : Variance.t list option }

  (** val ind_finite : mutual_inductive_body -> recursivity_kind **)

  let ind_finite m =
    m.ind_finite

  (** val ind_npars : mutual_inductive_body -> nat **)

  let ind_npars m =
    m.ind_npars

  (** val ind_params : mutual_inductive_body -> context **)

  let ind_params m =
    m.ind_params

  (** val ind_bodies : mutual_inductive_body -> one_inductive_body list **)

  let ind_bodies m =
    m.ind_bodies

  (** val ind_universes : mutual_inductive_body -> universes_decl **)

  let ind_universes m =
    m.ind_universes

  (** val ind_variance : mutual_inductive_body -> Variance.t list option **)

  let ind_variance m =
    m.ind_variance

  type constant_body = { cst_type : T.term; cst_body : T.term option;
                         cst_universes : universes_decl;
                         cst_relevance : relevance }

  (** val cst_type : constant_body -> T.term **)

  let cst_type c =
    c.cst_type

  (** val cst_body : constant_body -> T.term option **)

  let cst_body c =
    c.cst_body

  (** val cst_universes : constant_body -> universes_decl **)

  let cst_universes c =
    c.cst_universes

  (** val cst_relevance : constant_body -> relevance **)

  let cst_relevance c =
    c.cst_relevance

  (** val map_constant_body :
      (T.term -> T.term) -> constant_body -> constant_body **)

  let map_constant_body f decl =
    { cst_type = (f (cst_type decl)); cst_body =
      (option_map f (cst_body decl)); cst_universes = (cst_universes decl);
      cst_relevance = (cst_relevance decl) }

  type global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body

  (** val global_decl_rect :
      (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
      -> 'a1 **)

  let global_decl_rect f f0 = function
  | ConstantDecl c -> f c
  | InductiveDecl m -> f0 m

  (** val global_decl_rec :
      (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
      -> 'a1 **)

  let global_decl_rec f f0 = function
  | ConstantDecl c -> f c
  | InductiveDecl m -> f0 m

  (** val coq_NoConfusionPackage_global_decl :
      global_decl coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_global_decl =
    Build_NoConfusionPackage

  type global_declarations = (kername, global_decl) prod list

  type global_env = { universes : ContextSet.t;
                      declarations : global_declarations;
                      retroknowledge : Retroknowledge.t }

  (** val universes : global_env -> ContextSet.t **)

  let universes g =
    g.universes

  (** val declarations : global_env -> global_declarations **)

  let declarations g =
    g.declarations

  (** val retroknowledge : global_env -> Retroknowledge.t **)

  let retroknowledge g =
    g.retroknowledge

  (** val empty_global_env : global_env **)

  let empty_global_env =
    { universes = ContextSet.empty; declarations = Coq_nil; retroknowledge =
      Retroknowledge.empty }

  (** val add_global_decl :
      global_env -> (kername, global_decl) prod -> global_env **)

  let add_global_decl _UU03a3_ decl =
    { universes = (universes _UU03a3_); declarations = (Coq_cons (decl,
      (declarations _UU03a3_))); retroknowledge = (retroknowledge _UU03a3_) }

  (** val set_declarations :
      global_env -> global_declarations -> global_env **)

  let set_declarations _UU03a3_ decls =
    { universes = (universes _UU03a3_); declarations = decls;
      retroknowledge = (retroknowledge _UU03a3_) }

  (** val lookup_global :
      global_declarations -> kername -> global_decl option **)

  let rec lookup_global _UU03a3_ kn =
    match _UU03a3_ with
    | Coq_nil -> None
    | Coq_cons (d, tl) ->
      (match eqb Kername.reflect_kername kn (fst d) with
       | Coq_true -> Some (snd d)
       | Coq_false -> lookup_global tl kn)

  (** val lookup_env : global_env -> kername -> global_decl option **)

  let lookup_env _UU03a3_ kn =
    lookup_global (declarations _UU03a3_) kn

  (** val lookup_globals :
      global_declarations -> kername -> global_decl list **)

  let rec lookup_globals _UU03a3_ kn =
    match _UU03a3_ with
    | Coq_nil -> Coq_nil
    | Coq_cons (d, tl) ->
      let tl0 = lookup_globals tl kn in
      (match eqb Kername.reflect_kername kn (fst d) with
       | Coq_true -> Coq_cons ((snd d), tl0)
       | Coq_false -> tl0)

  (** val lookup_envs : global_env -> kername -> global_decl list **)

  let lookup_envs _UU03a3_ kn =
    lookup_globals (declarations _UU03a3_) kn

  type extends = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_decls = (__, kername -> (global_decl list, __) sigT, __) and3

  type extends_strictly_on_decls =
    (__, ((kername, global_decl) prod list, __) sigT, __) and3

  type strictly_extends_decls =
    (__, ((kername, global_decl) prod list, __) sigT, __) and3

  (** val strictly_extends_decls_extends_part_globals :
      (kername, global_decl) prod list -> (kername, global_decl) prod list ->
      ((kername, global_decl) prod list, __) sigT -> kername -> (global_decl
      list, __) sigT **)

  let strictly_extends_decls_extends_part_globals _ _ _top_assumption_ =
    let _evar_0_ = fun _x_ c -> Coq_existT ((lookup_globals _x_ c), __) in
    (fun c -> let Coq_existT (x, _) = _top_assumption_ in _evar_0_ x c)

  (** val strictly_extends_decls_extends_part :
      global_env -> global_env -> ((kername, global_decl) prod list, __) sigT
      -> kername -> (global_decl list, __) sigT **)

  let strictly_extends_decls_extends_part _UU03a3_ _UU03a3_' =
    strictly_extends_decls_extends_part_globals (declarations _UU03a3_)
      (declarations _UU03a3_')

  (** val strictly_extends_decls_extends_decls :
      global_env -> global_env -> strictly_extends_decls -> extends_decls **)

  let strictly_extends_decls_extends_decls _UU03a3_ _UU03a3_' _top_assumption_ =
    let { universes = _; declarations = declarations0; retroknowledge = _ } =
      _UU03a3_
    in
    let { universes = universes0; declarations = declarations1;
      retroknowledge = retroknowledge0 } = _UU03a3_'
    in
    let _evar_0_ = fun _p_ -> Times3 (__,
      (strictly_extends_decls_extends_part { universes = universes0;
        declarations = declarations0; retroknowledge = retroknowledge0 }
        { universes = universes0; declarations = declarations1;
        retroknowledge = retroknowledge0 } _p_), __)
    in
    let Times3 (_, p, _) = _top_assumption_ in _evar_0_ p

  (** val strictly_extends_decls_extends_strictly_on_decls :
      global_env -> global_env -> strictly_extends_decls ->
      extends_strictly_on_decls **)

  let strictly_extends_decls_extends_strictly_on_decls _ _ = function
  | Times3 (_, s, _) -> Times3 (__, s, __)

  (** val extends_decls_extends :
      global_env -> global_env -> extends_decls -> extends **)

  let extends_decls_extends _ _ = function
  | Times3 (_, s, _) -> Times3 (__, s, __)

  (** val extends_strictly_on_decls_extends :
      global_env -> global_env -> extends_strictly_on_decls -> extends **)

  let extends_strictly_on_decls_extends _UU03a3_ _UU03a3_' _top_assumption_ =
    let _evar_0_ = fun _p1_ -> Times3 (__,
      (strictly_extends_decls_extends_part _UU03a3_ _UU03a3_' _p1_), __)
    in
    let Times3 (_, p, _) = _top_assumption_ in _evar_0_ p

  (** val strictly_extends_decls_extends_decls_subrel :
      (global_env, strictly_extends_decls, extends_decls) subrelation **)

  let strictly_extends_decls_extends_decls_subrel =
    strictly_extends_decls_extends_decls

  (** val strictly_extends_decls_extends_strictly_on_decls_subrel :
      (global_env, strictly_extends_decls, extends_strictly_on_decls)
      subrelation **)

  let strictly_extends_decls_extends_strictly_on_decls_subrel =
    strictly_extends_decls_extends_strictly_on_decls

  (** val extends_decls_extends_subrel :
      (global_env, extends_decls, extends) subrelation **)

  let extends_decls_extends_subrel =
    extends_decls_extends

  (** val extends_strictly_on_decls_extends_subrel :
      (global_env, extends_strictly_on_decls, extends) subrelation **)

  let extends_strictly_on_decls_extends_subrel =
    extends_strictly_on_decls_extends

  (** val strictly_extends_decls_extends_subrel :
      (global_env, strictly_extends_decls, extends) subrelation **)

  let strictly_extends_decls_extends_subrel x y x0 =
    extends_strictly_on_decls_extends x y
      (strictly_extends_decls_extends_strictly_on_decls x y x0)

  (** val strictly_extends_decls_refl :
      (global_env, strictly_extends_decls) coq_Reflexive **)

  let strictly_extends_decls_refl _ =
    Times3 (__, (Coq_existT (Coq_nil, __)), __)

  (** val extends_decls_refl : (global_env, extends_decls) coq_Reflexive **)

  let extends_decls_refl _ =
    Times3 (__, (fun _ -> Coq_existT (Coq_nil, __)), __)

  (** val extends_strictly_on_decls_refl :
      (global_env, extends_strictly_on_decls) coq_Reflexive **)

  let extends_strictly_on_decls_refl _ =
    Times3 (__, (Coq_existT (Coq_nil, __)), __)

  (** val extends_refl : (global_env, extends) coq_Reflexive **)

  let extends_refl _ =
    Times3 (__, (fun _ -> Coq_existT (Coq_nil, __)), __)

  (** val extends_decls_part_globals_refl :
      global_declarations -> kername -> (global_decl list, __) sigT **)

  let extends_decls_part_globals_refl _ _ =
    Coq_existT (Coq_nil, __)

  (** val extends_decls_part_refl :
      global_env -> kername -> (global_decl list, __) sigT **)

  let extends_decls_part_refl _UU03a3_ =
    extends_decls_part_globals_refl (declarations _UU03a3_)

  (** val strictly_extends_decls_part_globals_refl :
      global_declarations -> ((kername, global_decl) prod list, __) sigT **)

  let strictly_extends_decls_part_globals_refl _ =
    Coq_existT (Coq_nil, __)

  (** val strictly_extends_decls_part_refl :
      global_env -> ((kername, global_decl) prod list, __) sigT **)

  let strictly_extends_decls_part_refl _UU03a3_ =
    strictly_extends_decls_part_globals_refl (declarations _UU03a3_)

  (** val extends_decls_part_globals_trans :
      global_declarations -> global_declarations -> global_declarations ->
      (kername -> (global_decl list, __) sigT) -> (kername -> (global_decl
      list, __) sigT) -> kername -> (global_decl list, __) sigT **)

  let extends_decls_part_globals_trans _ _ _ h1 h2 c =
    let __top_assumption_ = h1 c in
    let _evar_0_ = fun _x_ __top_assumption_0 ->
      let _evar_0_ = fun _x1_ -> Coq_existT ((app _x1_ _x_), __) in
      let Coq_existT (x, _) = __top_assumption_0 in _evar_0_ x
    in
    let Coq_existT (x, _) = __top_assumption_ in _evar_0_ x (h2 c)

  (** val extends_decls_part_trans :
      global_env -> global_env -> global_env -> (kername -> (global_decl
      list, __) sigT) -> (kername -> (global_decl list, __) sigT) -> kername
      -> (global_decl list, __) sigT **)

  let extends_decls_part_trans _UU03a3_ _UU03a3_' _UU03a3_'' =
    extends_decls_part_globals_trans (declarations _UU03a3_)
      (declarations _UU03a3_') (declarations _UU03a3_'')

  (** val strictly_extends_decls_part_globals_trans :
      global_declarations -> global_declarations -> global_declarations ->
      ((kername, global_decl) prod list, __) sigT -> ((kername, global_decl)
      prod list, __) sigT -> ((kername, global_decl) prod list, __) sigT **)

  let strictly_extends_decls_part_globals_trans _ _ _ __top_assumption_ =
    let _evar_0_ = fun _x_ __top_assumption_0 ->
      let _evar_0_ = fun _x1_ -> Coq_existT ((app _x1_ _x_), __) in
      let Coq_existT (x, _) = __top_assumption_0 in _evar_0_ x
    in
    (fun __top_assumption_0 ->
    let Coq_existT (x, _) = __top_assumption_ in _evar_0_ x __top_assumption_0)

  (** val strictly_extends_decls_part_trans :
      global_env -> global_env -> global_env -> ((kername, global_decl) prod
      list, __) sigT -> ((kername, global_decl) prod list, __) sigT ->
      ((kername, global_decl) prod list, __) sigT **)

  let strictly_extends_decls_part_trans _UU03a3_ _UU03a3_' _UU03a3_'' =
    strictly_extends_decls_part_globals_trans (declarations _UU03a3_)
      (declarations _UU03a3_') (declarations _UU03a3_'')

  (** val strictly_extends_decls_trans :
      (global_env, strictly_extends_decls) coq_Transitive **)

  let strictly_extends_decls_trans x y z x0 x1 =
    let { universes = _; declarations = declarations0; retroknowledge = _ } =
      x
    in
    let { universes = _; declarations = declarations1; retroknowledge = _ } =
      y
    in
    let { universes = _; declarations = declarations2; retroknowledge = _ } =
      z
    in
    let Times3 (_, s, _) = x0 in
    let Times3 (_, s0, _) = x1 in
    Times3 (__,
    (strictly_extends_decls_part_globals_trans declarations0 declarations1
      declarations2 s s0), __)

  (** val extends_decls_trans : (global_env, extends_decls) coq_Transitive **)

  let extends_decls_trans x y z x0 x1 =
    let { universes = _; declarations = declarations0; retroknowledge = _ } =
      x
    in
    let { universes = _; declarations = declarations1; retroknowledge = _ } =
      y
    in
    let { universes = _; declarations = declarations2; retroknowledge = _ } =
      z
    in
    let Times3 (_, s, _) = x0 in
    let Times3 (_, s0, _) = x1 in
    Times3 (__,
    (extends_decls_part_globals_trans declarations0 declarations1
      declarations2 s s0), __)

  (** val extends_strictly_on_decls_trans :
      (global_env, extends_strictly_on_decls) coq_Transitive **)

  let extends_strictly_on_decls_trans x y z x0 x1 =
    let { universes = _; declarations = declarations0; retroknowledge = _ } =
      x
    in
    let { universes = _; declarations = declarations1; retroknowledge = _ } =
      y
    in
    let { universes = _; declarations = declarations2; retroknowledge = _ } =
      z
    in
    let Times3 (_, s, _) = x0 in
    let Times3 (_, s0, _) = x1 in
    Times3 (__,
    (strictly_extends_decls_part_globals_trans declarations0 declarations1
      declarations2 s s0), __)

  (** val extends_trans : (global_env, extends) coq_Transitive **)

  let extends_trans x y z x0 x1 =
    let { universes = _; declarations = declarations0; retroknowledge = _ } =
      x
    in
    let { universes = _; declarations = declarations1; retroknowledge = _ } =
      y
    in
    let { universes = _; declarations = declarations2; retroknowledge = _ } =
      z
    in
    let Times3 (_, s, _) = x0 in
    let Times3 (_, s0, _) = x1 in
    Times3 (__,
    (extends_decls_part_globals_trans declarations0 declarations1
      declarations2 s s0), __)

  (** val declared_kername_set : global_declarations -> KernameSet.t **)

  let declared_kername_set _UU03a3_ =
    fold_right KernameSet.add KernameSet.empty (map fst _UU03a3_)

  (** val merge_globals :
      global_declarations -> global_declarations -> global_declarations **)

  let merge_globals _UU03a3_ _UU03a3_' =
    let known_kns = declared_kername_set _UU03a3_ in
    app
      (filter (fun pat ->
        let Coq_pair (kn, _) = pat in negb (KernameSet.mem kn known_kns))
        _UU03a3_') _UU03a3_

  (** val merge_global_envs : global_env -> global_env -> global_env **)

  let merge_global_envs _UU03a3_ _UU03a3_' =
    { universes =
      (ContextSet.union (universes _UU03a3_) (universes _UU03a3_'));
      declarations =
      (merge_globals (declarations _UU03a3_) (declarations _UU03a3_'));
      retroknowledge =
      (Retroknowledge.merge (retroknowledge _UU03a3_)
        (retroknowledge _UU03a3_')) }

  (** val strictly_extends_decls_l_merge_globals :
      global_declarations -> global_declarations -> ((kername, global_decl)
      prod list, __) sigT **)

  let strictly_extends_decls_l_merge_globals _UU03a3_ _UU03a3_' =
    Coq_existT
      ((filter (fun pat ->
         let Coq_pair (kn, _) = pat in
         negb (KernameSet.mem kn (declared_kername_set _UU03a3_))) _UU03a3_'),
      __)

  (** val extends_l_merge_globals :
      global_declarations -> global_declarations -> kername -> (global_decl
      list, __) sigT **)

  let extends_l_merge_globals _UU03a3_ _UU03a3_' c =
    Coq_existT
      ((match negb (KernameSet.mem c (declared_kername_set _UU03a3_)) with
        | Coq_true -> lookup_globals _UU03a3_' c
        | Coq_false -> Coq_nil), __)

  (** val extends_strictly_on_decls_l_merge :
      global_env -> global_env -> extends_strictly_on_decls **)

  let extends_strictly_on_decls_l_merge _UU03a3_ _UU03a3_' =
    Times3 (__,
      (strictly_extends_decls_l_merge_globals (declarations _UU03a3_)
        (declarations _UU03a3_')), __)

  (** val extends_l_merge : global_env -> global_env -> extends **)

  let extends_l_merge _UU03a3_ _UU03a3_' =
    extends_strictly_on_decls_extends _UU03a3_
      (merge_global_envs _UU03a3_ _UU03a3_')
      (extends_strictly_on_decls_l_merge _UU03a3_ _UU03a3_')

  (** val extends_r_merge_globals :
      global_declarations -> global_declarations -> kername -> (global_decl
      list, __) sigT **)

  let extends_r_merge_globals _UU03a3_ _UU03a3_' c =
    let s =
      in_dec (eq_dec (coq_ReflectEq_EqDec Kername.reflect_kername)) c
        (map fst _UU03a3_')
    in
    (match s with
     | Coq_left -> Coq_existT (Coq_nil, __)
     | Coq_right -> Coq_existT ((lookup_globals _UU03a3_ c), __))

  (** val extends_r_merge : global_env -> global_env -> extends **)

  let extends_r_merge _UU03a3_ _UU03a3_' =
    Times3 (__,
      (extends_r_merge_globals (declarations _UU03a3_)
        (declarations _UU03a3_')), __)

  (** val primitive_constant : global_env -> prim_tag -> kername option **)

  let primitive_constant _UU03a3_ = function
  | Coq_primInt -> (retroknowledge _UU03a3_).Retroknowledge.retro_int63
  | Coq_primFloat -> (retroknowledge _UU03a3_).Retroknowledge.retro_float64

  type primitive_invariants = (Universe.t, __) sigT

  type global_env_ext = (global_env, universes_decl) prod

  (** val fst_ctx : global_env_ext -> global_env **)

  let fst_ctx =
    fst

  (** val empty_ext : global_env -> global_env_ext **)

  let empty_ext _UU03a3_ =
    Coq_pair (_UU03a3_, Monomorphic_ctx)

  type program = (global_env, T.term) prod

  (** val app_context : context -> context -> context **)

  let app_context _UU0393_ _UU0393_' =
    app _UU0393_' _UU0393_

  (** val mkLambda_or_LetIn : T.term context_decl -> T.term -> T.term **)

  let mkLambda_or_LetIn d t0 =
    match d.decl_body with
    | Some b -> T.tLetIn d.decl_name b d.decl_type t0
    | None -> T.tLambda d.decl_name d.decl_type t0

  (** val it_mkLambda_or_LetIn : context -> T.term -> T.term **)

  let it_mkLambda_or_LetIn l t0 =
    fold_left (fun acc d -> mkLambda_or_LetIn d acc) l t0

  (** val mkProd_or_LetIn : T.term context_decl -> T.term -> T.term **)

  let mkProd_or_LetIn d t0 =
    match d.decl_body with
    | Some b -> T.tLetIn d.decl_name b d.decl_type t0
    | None -> T.tProd d.decl_name d.decl_type t0

  (** val it_mkProd_or_LetIn : context -> T.term -> T.term **)

  let it_mkProd_or_LetIn l t0 =
    fold_left (fun acc d -> mkProd_or_LetIn d acc) l t0

  (** val reln :
      T.term list -> nat -> T.term context_decl list -> T.term list **)

  let rec reln l p = function
  | Coq_nil -> l
  | Coq_cons (c, hyps) ->
    let { decl_name = _; decl_body = decl_body0; decl_type = _ } = c in
    (match decl_body0 with
     | Some _ -> reln l (add p (S O)) hyps
     | None -> reln (Coq_cons ((T.tRel p), l)) (add p (S O)) hyps)

  (** val to_extended_list_k :
      T.term context_decl list -> nat -> T.term list **)

  let to_extended_list_k _UU0393_ k =
    reln Coq_nil k _UU0393_

  (** val to_extended_list : T.term context_decl list -> T.term list **)

  let to_extended_list _UU0393_ =
    to_extended_list_k _UU0393_ O

  (** val reln_alt : nat -> context -> T.term list **)

  let rec reln_alt p = function
  | Coq_nil -> Coq_nil
  | Coq_cons (c, _UU0393_0) ->
    let { decl_name = _; decl_body = decl_body0; decl_type = _ } = c in
    (match decl_body0 with
     | Some _ -> reln_alt (add p (S O)) _UU0393_0
     | None -> Coq_cons ((T.tRel p), (reln_alt (add p (S O)) _UU0393_0)))

  (** val arities_context :
      one_inductive_body list -> T.term context_decl list **)

  let arities_context l =
    rev_map (fun ind ->
      vass { binder_name = (Coq_nNamed (ind_name ind)); binder_relevance =
        (ind_relevance ind) } (ind_type ind)) l

  (** val map_mutual_inductive_body :
      (nat -> T.term -> T.term) -> mutual_inductive_body ->
      mutual_inductive_body **)

  let map_mutual_inductive_body f m =
    let { ind_finite = finite; ind_npars = ind_npars0; ind_params = ind_pars;
      ind_bodies = ind_bodies0; ind_universes = ind_universes0;
      ind_variance = ind_variance0 } = m
    in
    let arities = arities_context ind_bodies0 in
    let pars = fold_context_k f ind_pars in
    { ind_finite = finite; ind_npars = ind_npars0; ind_params = pars;
    ind_bodies =
    (map
      (map_one_inductive_body (context_assumptions pars) (length arities) f)
      ind_bodies0); ind_universes = ind_universes0; ind_variance =
    ind_variance0 }

  (** val projs : inductive -> nat -> nat -> T.term list **)

  let rec projs ind npars = function
  | O -> Coq_nil
  | S k' ->
    Coq_cons
      ((T.tProj { proj_ind = ind; proj_npars = npars; proj_arg = k' }
         (T.tRel O)), (projs ind npars k'))

  type 'p coq_All_decls =
  | Coq_on_vass of aname * T.term * T.term * 'p
  | Coq_on_vdef of aname * T.term * T.term * T.term * T.term * 'p * 'p

  (** val coq_All_decls_rect :
      (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
      -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
      T.term context_decl -> 'a1 coq_All_decls -> 'a2 **)

  let coq_All_decls_rect f f0 _ _ = function
  | Coq_on_vass (na, t0, t', p) -> f na t0 t' p
  | Coq_on_vdef (na, b, t0, b', t', p, p0) -> f0 na b t0 b' t' p p0

  (** val coq_All_decls_rec :
      (aname -> T.term -> T.term -> 'a1 -> 'a2) -> (aname -> T.term -> T.term
      -> T.term -> T.term -> 'a1 -> 'a1 -> 'a2) -> T.term context_decl ->
      T.term context_decl -> 'a1 coq_All_decls -> 'a2 **)

  let coq_All_decls_rec f f0 _ _ = function
  | Coq_on_vass (na, t0, t', p) -> f na t0 t' p
  | Coq_on_vdef (na, b, t0, b', t', p, p0) -> f0 na b t0 b' t' p p0

  type 'p coq_All_decls_sig = 'p coq_All_decls

  (** val coq_All_decls_sig_pack :
      T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
      (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls **)

  let coq_All_decls_sig_pack x x0 all_decls_var =
    (x,x0),all_decls_var

  (** val coq_All_decls_Signature :
      T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls,
      T.term context_decl * T.term context_decl, 'a1 coq_All_decls_sig)
      coq_Signature **)

  let coq_All_decls_Signature =
    coq_All_decls_sig_pack

  (** val coq_NoConfusionPackage_All_decls :
      ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls)
      coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_All_decls =
    Build_NoConfusionPackage

  type 'p coq_All_decls_alpha =
  | Coq_on_vass_alpha of name binder_annot * name binder_annot * T.term
     * T.term * 'p
  | Coq_on_vdef_alpha of name binder_annot * name binder_annot * T.term
     * T.term * T.term * T.term * 'p * 'p

  (** val coq_All_decls_alpha_rect :
      (name binder_annot -> name binder_annot -> T.term -> T.term -> __ ->
      'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
      T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
      context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2 **)

  let coq_All_decls_alpha_rect f f0 _ _ = function
  | Coq_on_vass_alpha (na, na', t0, t', p) -> f na na' t0 t' __ p
  | Coq_on_vdef_alpha (na, na', b, t0, b', t', p, p0) ->
    f0 na na' b t0 b' t' __ p p0

  (** val coq_All_decls_alpha_rec :
      (name binder_annot -> name binder_annot -> T.term -> T.term -> __ ->
      'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> T.term ->
      T.term -> T.term -> T.term -> __ -> 'a1 -> 'a1 -> 'a2) -> T.term
      context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha -> 'a2 **)

  let coq_All_decls_alpha_rec f f0 _ _ = function
  | Coq_on_vass_alpha (na, na', t0, t', p) -> f na na' t0 t' __ p
  | Coq_on_vdef_alpha (na, na', b, t0, b', t', p, p0) ->
    f0 na na' b t0 b' t' __ p p0

  type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

  (** val coq_All_decls_alpha_sig_pack :
      T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha
      -> (T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha **)

  let coq_All_decls_alpha_sig_pack x x0 all_decls_alpha_var =
    (x,x0),all_decls_alpha_var

  (** val coq_All_decls_alpha_Signature :
      T.term context_decl -> T.term context_decl -> ('a1 coq_All_decls_alpha,
      T.term context_decl * T.term context_decl, 'a1 coq_All_decls_alpha_sig)
      coq_Signature **)

  let coq_All_decls_alpha_Signature =
    coq_All_decls_alpha_sig_pack

  (** val coq_NoConfusionPackage_All_decls_alpha :
      ((T.term context_decl * T.term context_decl) * 'a1 coq_All_decls_alpha)
      coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_All_decls_alpha =
    Build_NoConfusionPackage

  (** val coq_All_decls_impl :
      T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls ->
      (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls **)

  let coq_All_decls_impl _ _ ond h =
    match ond with
    | Coq_on_vass (na, t0, t', p) -> Coq_on_vass (na, t0, t', (h t0 t' p))
    | Coq_on_vdef (na, b, t0, b', t', p, p0) ->
      Coq_on_vdef (na, b, t0, b', t', (h b b' p), (h t0 t' p0))

  (** val coq_All_decls_alpha_impl :
      T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls_alpha
      -> (T.term -> T.term -> 'a1 -> 'a2) -> 'a2 coq_All_decls_alpha **)

  let coq_All_decls_alpha_impl _ _ ond h =
    match ond with
    | Coq_on_vass_alpha (na, na', t0, t', p) ->
      Coq_on_vass_alpha (na, na', t0, t', (h t0 t' p))
    | Coq_on_vdef_alpha (na, na', b, t0, b', t', p, p0) ->
      Coq_on_vdef_alpha (na, na', b, t0, b', t', (h b b' p), (h t0 t' p0))

  (** val coq_All_decls_to_alpha :
      T.term context_decl -> T.term context_decl -> 'a1 coq_All_decls -> 'a1
      coq_All_decls_alpha **)

  let coq_All_decls_to_alpha _ _ = function
  | Coq_on_vass (na, t0, t', p) -> Coq_on_vass_alpha (na, na, t0, t', p)
  | Coq_on_vdef (na, b, t0, b', t', p, p0) ->
    Coq_on_vdef_alpha (na, na, b, t0, b', t', p, p0)

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

module EnvironmentDecideReflectInstances =
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
 struct
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
