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
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val isSort : term -> bool **)

let isSort = function
| Coq_tSort _ -> Coq_true
| _ -> Coq_false

(** val isArity : term -> bool **)

let rec isArity = function
| Coq_tSort _ -> Coq_true
| Coq_tProd (_, _, codom) -> isArity codom
| Coq_tLetIn (_, _, _, codom) -> isArity codom
| _ -> Coq_false

(** val type_of_constructor :
    Env.mutual_inductive_body -> Env.constructor_body -> (inductive, nat)
    prod -> Level.t list -> term **)

let type_of_constructor mdecl cdecl c u =
  let mind = (fst c).inductive_mind in
  subst (inds mind u (Env.ind_bodies mdecl)) O
    (subst_instance subst_instance_constr u (Env.cstr_type cdecl))

(** val fix_subst : term mfixpoint -> term list **)

let fix_subst l =
  let rec aux = function
  | O -> Coq_nil
  | S n0 -> Coq_cons ((Coq_tFix (l, n0)), (aux n0))
  in aux (length l)

(** val unfold_fix : term mfixpoint -> nat -> (nat, term) prod option **)

let unfold_fix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (Coq_pair (d.rarg, (subst (fix_subst mfix) O d.dbody)))
  | None -> None

(** val cofix_subst : term mfixpoint -> term list **)

let cofix_subst l =
  let rec aux = function
  | O -> Coq_nil
  | S n0 -> Coq_cons ((Coq_tCoFix (l, n0)), (aux n0))
  in aux (length l)

(** val unfold_cofix : term mfixpoint -> nat -> (nat, term) prod option **)

let unfold_cofix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (Coq_pair (d.rarg, (subst (cofix_subst mfix) O d.dbody)))
  | None -> None

(** val is_constructor : nat -> term list -> bool **)

let is_constructor n ts =
  match nth_error ts n with
  | Some a -> isConstruct_app a
  | None -> Coq_false

(** val fix_context : term mfixpoint -> Env.context **)

let fix_context m =
  List.rev (mapi (fun i d -> Env.vass d.dname (lift i O d.dtype)) m)

(** val dummy_branch : term branch **)

let dummy_branch =
  { bcontext = Coq_nil; bbody = tDummy }

(** val iota_red : nat -> term list -> Env.context -> term branch -> term **)

let iota_red npar args bctx br =
  subst (List.rev (skipn npar args)) O (Env.expand_lets bctx br.bbody)

(** val instantiate_params_subst_spec_sig_pack :
    Env.context -> term list -> term list -> term -> term list -> term ->
    (Env.context * (term list * (term list * (term * (term
    list * term))))) * __ **)

let instantiate_params_subst_spec_sig_pack x x0 x1 x2 x3 x4 =
  (x,(x0,(x1,(x2,(x3,x4))))),__

(** val instantiate_params_subst_spec_Signature :
    Env.context -> term list -> term list -> term -> term list -> term ->
    (Env.context * (term list * (term list * (term * (term
    list * term))))) * __ **)

let instantiate_params_subst_spec_Signature x x0 x1 x2 x3 x4 =
  (x,(x0,(x1,(x2,(x3,x4))))),__

(** val instantiate_params_subst :
    Env.context -> term list -> term list -> term -> (term list, term) prod
    option **)

let rec instantiate_params_subst params pars s ty =
  match params with
  | Coq_nil ->
    (match pars with
     | Coq_nil -> Some (Coq_pair (s, ty))
     | Coq_cons (_, _) -> None)
  | Coq_cons (d, params0) ->
    (match d.decl_body with
     | Some b ->
       (match ty with
        | Coq_tLetIn (_, _, _, b') ->
          instantiate_params_subst params0 pars (Coq_cons ((subst s O b), s))
            b'
        | _ -> None)
     | None ->
       (match ty with
        | Coq_tProd (_, _, b) ->
          (match pars with
           | Coq_nil -> None
           | Coq_cons (hd, tl) ->
             instantiate_params_subst params0 tl (Coq_cons (hd, s)) b)
        | _ -> None))

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

(** val red1_rect :
    Env.global_env -> (Env.context -> aname -> term -> term -> term -> term
    list -> 'a1) -> (Env.context -> aname -> term -> term -> term -> 'a1) ->
    (Env.context -> nat -> term -> __ -> 'a1) -> (Env.context -> case_info ->
    Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.constructor_body -> nat -> Instance.t -> term list -> term predicate
    -> term branch list -> term branch -> __ -> __ -> __ -> 'a1) ->
    (Env.context -> term mfixpoint -> nat -> term list -> nat -> term -> __
    -> __ -> 'a1) -> (Env.context -> case_info -> term predicate -> term
    mfixpoint -> nat -> term list -> nat -> term -> term branch list -> __ ->
    'a1) -> (Env.context -> projection -> term mfixpoint -> nat -> term list
    -> nat -> term -> __ -> 'a1) -> (Env.context -> kername ->
    Env.constant_body -> term -> __ -> Instance.t -> __ -> 'a1) ->
    (Env.context -> projection -> Instance.t -> term list -> term -> __ ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> term -> red1 ->
    'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term ->
    red1 -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term ->
    term -> red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term list ->
    term list -> Instance.t -> aname list -> term -> term -> term branch list
    -> (term, red1) coq_OnOne2 -> 'a1) -> (Env.context -> case_info ->
    Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> term list ->
    Instance.t -> aname list -> term -> term -> term -> term branch list ->
    red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term predicate ->
    term -> term -> term branch list -> red1 -> 'a1 -> 'a1) -> (Env.context
    -> case_info -> Env.mutual_inductive_body -> Env.one_inductive_body -> __
    -> term predicate -> term -> term branch list -> term branch list ->
    (term branch, Env.context, (red1, __) prod) coq_OnOne2All -> 'a1) ->
    (Env.context -> projection -> term -> term -> red1 -> 'a1 -> 'a1) ->
    (Env.context -> term -> term -> term list -> red1 -> 'a1 -> 'a1) ->
    (Env.context -> term list -> term list -> term -> (term, red1) coq_OnOne2
    -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1
    -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1
    -> 'a1) -> (Env.context -> nat -> term list -> term list -> (term, red1)
    coq_OnOne2 -> 'a1) -> (Env.context -> term -> cast_kind -> term -> term
    -> red1 -> 'a1 -> 'a1) -> (Env.context -> term -> cast_kind -> term ->
    term -> red1 -> 'a1 -> 'a1) -> (Env.context -> term -> cast_kind -> term
    -> 'a1) -> (Env.context -> term def list -> term def list -> nat -> (term
    def, (red1, __) prod) coq_OnOne2 -> 'a1) -> (Env.context -> term
    mfixpoint -> term def list -> nat -> (term def, (red1, __) prod)
    coq_OnOne2 -> 'a1) -> (Env.context -> term def list -> term def list ->
    nat -> (term def, (red1, __) prod) coq_OnOne2 -> 'a1) -> (Env.context ->
    term mfixpoint -> term def list -> nat -> (term def, (red1, __) prod)
    coq_OnOne2 -> 'a1) -> Env.context -> term -> term -> red1 -> 'a1 **)

let rec red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ _ _ = function
| Coq_red_beta (na, t0, b, a, l) -> f _UU0393_ na t0 b a l
| Coq_red_zeta (na, b, t0, b') -> f0 _UU0393_ na b t0 b'
| Coq_red_rel (i, body) -> f1 _UU0393_ i body __
| Coq_red_iota (ci, mdecl, idecl, cdecl, c, u, args, p, brs, br) ->
  f2 _UU0393_ ci mdecl idecl cdecl c u args p brs br __ __ __
| Coq_red_fix (mfix, idx, args, narg, fn) ->
  f3 _UU0393_ mfix idx args narg fn __ __
| Coq_red_cofix_case (ip, p, mfix, idx, args, narg, fn, brs) ->
  f4 _UU0393_ ip p mfix idx args narg fn brs __
| Coq_red_cofix_proj (p, mfix, idx, args, narg, fn) ->
  f5 _UU0393_ p mfix idx args narg fn __
| Coq_red_delta (c, decl, body, u) -> f6 _UU0393_ c decl body __ u __
| Coq_red_proj (p, u, args, arg) -> f7 _UU0393_ p u args arg __
| Coq_abs_red_l (na, m, m', n, r0) ->
  f8 _UU0393_ na m m' n r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m
      m' r0)
| Coq_abs_red_r (na, m, m', n, r0) ->
  f9 _UU0393_ na m m' n r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (snoc _UU0393_ (Env.vass na n)) m m' r0)
| Coq_letin_red_def (na, b, t0, b', r0, r1) ->
  f10 _UU0393_ na b t0 b' r0 r1
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ b
      r0 r1)
| Coq_letin_red_ty (na, b, t0, b', r0, r1) ->
  f11 _UU0393_ na b t0 b' r0 r1
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ t0
      r0 r1)
| Coq_letin_red_body (na, b, t0, b', r0, r1) ->
  f12 _UU0393_ na b t0 b' r0 r1
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (snoc _UU0393_ (Env.vdef na b t0)) b' r0 r1)
| Coq_case_red_pred_param (ind, params, params', puinst0, pcontext0,
                           preturn0, c, brs, o) ->
  f13 _UU0393_ ind params params' puinst0 pcontext0 preturn0 c brs o
| Coq_case_red_pred_return (ind, mdecl, idecl, params, puinst0, pcontext0,
                            preturn0, preturn', c, brs, x) ->
  let p = { puinst = puinst0; pparams = params; pcontext = pcontext0;
    preturn = preturn0 }
  in
  f14 _UU0393_ ind mdecl idecl __ params puinst0 pcontext0 preturn0 preturn'
    c brs x
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (Env.app_context _UU0393_
        (case_predicate_context ind.ci_ind mdecl idecl p)) preturn0 preturn'
      x)
| Coq_case_red_discr (ind, p, c, c', brs, r0) ->
  f15 _UU0393_ ind p c c' brs r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ c
      c' r0)
| Coq_case_red_brs (ind, mdecl, idecl, p, c, brs, brs', o) ->
  f16 _UU0393_ ind mdecl idecl __ p c brs brs' o
| Coq_proj_red (p, c, c', r0) ->
  f17 _UU0393_ p c c' r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ c
      c' r0)
| Coq_app_red_l (m1, n1, m2, r0) ->
  f18 _UU0393_ m1 n1 m2 r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m1
      n1 r0)
| Coq_app_red_r (m2, n2, m1, o) -> f19 _UU0393_ m2 n2 m1 o
| Coq_prod_red_l (na, m1, m2, n1, r0) ->
  f20 _UU0393_ na m1 m2 n1 r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m1
      n1 r0)
| Coq_prod_red_r (na, m2, n2, m1, r0) ->
  f21 _UU0393_ na m2 n2 m1 r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (snoc _UU0393_ (Env.vass na m1)) m2 n2 r0)
| Coq_evar_red (ev, l, l', o) -> f22 _UU0393_ ev l l' o
| Coq_cast_red_l (m1, k, m2, n1, r0) ->
  f23 _UU0393_ m1 k m2 n1 r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m1
      n1 r0)
| Coq_cast_red_r (m2, k, n2, m1, r0) ->
  f24 _UU0393_ m2 k n2 m1 r0
    (red1_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m2
      n2 r0)
| Coq_cast_red (m1, k, m2) -> f25 _UU0393_ m1 k m2
| Coq_fix_red_ty (mfix0, mfix1, idx, o) -> f26 _UU0393_ mfix0 mfix1 idx o
| Coq_fix_red_body (mfix0, mfix1, idx, o) -> f27 _UU0393_ mfix0 mfix1 idx o
| Coq_cofix_red_ty (mfix0, mfix1, idx, o) -> f28 _UU0393_ mfix0 mfix1 idx o
| Coq_cofix_red_body (mfix0, mfix1, idx, o) -> f29 _UU0393_ mfix0 mfix1 idx o

(** val red1_rec :
    Env.global_env -> (Env.context -> aname -> term -> term -> term -> term
    list -> 'a1) -> (Env.context -> aname -> term -> term -> term -> 'a1) ->
    (Env.context -> nat -> term -> __ -> 'a1) -> (Env.context -> case_info ->
    Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.constructor_body -> nat -> Instance.t -> term list -> term predicate
    -> term branch list -> term branch -> __ -> __ -> __ -> 'a1) ->
    (Env.context -> term mfixpoint -> nat -> term list -> nat -> term -> __
    -> __ -> 'a1) -> (Env.context -> case_info -> term predicate -> term
    mfixpoint -> nat -> term list -> nat -> term -> term branch list -> __ ->
    'a1) -> (Env.context -> projection -> term mfixpoint -> nat -> term list
    -> nat -> term -> __ -> 'a1) -> (Env.context -> kername ->
    Env.constant_body -> term -> __ -> Instance.t -> __ -> 'a1) ->
    (Env.context -> projection -> Instance.t -> term list -> term -> __ ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> term -> red1 ->
    'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term ->
    red1 -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term ->
    term -> red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term list ->
    term list -> Instance.t -> aname list -> term -> term -> term branch list
    -> (term, red1) coq_OnOne2 -> 'a1) -> (Env.context -> case_info ->
    Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> term list ->
    Instance.t -> aname list -> term -> term -> term -> term branch list ->
    red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term predicate ->
    term -> term -> term branch list -> red1 -> 'a1 -> 'a1) -> (Env.context
    -> case_info -> Env.mutual_inductive_body -> Env.one_inductive_body -> __
    -> term predicate -> term -> term branch list -> term branch list ->
    (term branch, Env.context, (red1, __) prod) coq_OnOne2All -> 'a1) ->
    (Env.context -> projection -> term -> term -> red1 -> 'a1 -> 'a1) ->
    (Env.context -> term -> term -> term list -> red1 -> 'a1 -> 'a1) ->
    (Env.context -> term list -> term list -> term -> (term, red1) coq_OnOne2
    -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1
    -> 'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1
    -> 'a1) -> (Env.context -> nat -> term list -> term list -> (term, red1)
    coq_OnOne2 -> 'a1) -> (Env.context -> term -> cast_kind -> term -> term
    -> red1 -> 'a1 -> 'a1) -> (Env.context -> term -> cast_kind -> term ->
    term -> red1 -> 'a1 -> 'a1) -> (Env.context -> term -> cast_kind -> term
    -> 'a1) -> (Env.context -> term def list -> term def list -> nat -> (term
    def, (red1, __) prod) coq_OnOne2 -> 'a1) -> (Env.context -> term
    mfixpoint -> term def list -> nat -> (term def, (red1, __) prod)
    coq_OnOne2 -> 'a1) -> (Env.context -> term def list -> term def list ->
    nat -> (term def, (red1, __) prod) coq_OnOne2 -> 'a1) -> (Env.context ->
    term mfixpoint -> term def list -> nat -> (term def, (red1, __) prod)
    coq_OnOne2 -> 'a1) -> Env.context -> term -> term -> red1 -> 'a1 **)

let rec red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ _ _ = function
| Coq_red_beta (na, t0, b, a, l) -> f _UU0393_ na t0 b a l
| Coq_red_zeta (na, b, t0, b') -> f0 _UU0393_ na b t0 b'
| Coq_red_rel (i, body) -> f1 _UU0393_ i body __
| Coq_red_iota (ci, mdecl, idecl, cdecl, c, u, args, p, brs, br) ->
  f2 _UU0393_ ci mdecl idecl cdecl c u args p brs br __ __ __
| Coq_red_fix (mfix, idx, args, narg, fn) ->
  f3 _UU0393_ mfix idx args narg fn __ __
| Coq_red_cofix_case (ip, p, mfix, idx, args, narg, fn, brs) ->
  f4 _UU0393_ ip p mfix idx args narg fn brs __
| Coq_red_cofix_proj (p, mfix, idx, args, narg, fn) ->
  f5 _UU0393_ p mfix idx args narg fn __
| Coq_red_delta (c, decl, body, u) -> f6 _UU0393_ c decl body __ u __
| Coq_red_proj (p, u, args, arg) -> f7 _UU0393_ p u args arg __
| Coq_abs_red_l (na, m, m', n, r0) ->
  f8 _UU0393_ na m m' n r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m
      m' r0)
| Coq_abs_red_r (na, m, m', n, r0) ->
  f9 _UU0393_ na m m' n r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (snoc _UU0393_ (Env.vass na n)) m m' r0)
| Coq_letin_red_def (na, b, t0, b', r0, r1) ->
  f10 _UU0393_ na b t0 b' r0 r1
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ b
      r0 r1)
| Coq_letin_red_ty (na, b, t0, b', r0, r1) ->
  f11 _UU0393_ na b t0 b' r0 r1
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ t0
      r0 r1)
| Coq_letin_red_body (na, b, t0, b', r0, r1) ->
  f12 _UU0393_ na b t0 b' r0 r1
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (snoc _UU0393_ (Env.vdef na b t0)) b' r0 r1)
| Coq_case_red_pred_param (ind, params, params', puinst0, pcontext0,
                           preturn0, c, brs, o) ->
  f13 _UU0393_ ind params params' puinst0 pcontext0 preturn0 c brs o
| Coq_case_red_pred_return (ind, mdecl, idecl, params, puinst0, pcontext0,
                            preturn0, preturn', c, brs, x) ->
  let p = { puinst = puinst0; pparams = params; pcontext = pcontext0;
    preturn = preturn0 }
  in
  f14 _UU0393_ ind mdecl idecl __ params puinst0 pcontext0 preturn0 preturn'
    c brs x
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (Env.app_context _UU0393_
        (case_predicate_context ind.ci_ind mdecl idecl p)) preturn0 preturn'
      x)
| Coq_case_red_discr (ind, p, c, c', brs, r0) ->
  f15 _UU0393_ ind p c c' brs r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ c
      c' r0)
| Coq_case_red_brs (ind, mdecl, idecl, p, c, brs, brs', o) ->
  f16 _UU0393_ ind mdecl idecl __ p c brs brs' o
| Coq_proj_red (p, c, c', r0) ->
  f17 _UU0393_ p c c' r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ c
      c' r0)
| Coq_app_red_l (m1, n1, m2, r0) ->
  f18 _UU0393_ m1 n1 m2 r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m1
      n1 r0)
| Coq_app_red_r (m2, n2, m1, o) -> f19 _UU0393_ m2 n2 m1 o
| Coq_prod_red_l (na, m1, m2, n1, r0) ->
  f20 _UU0393_ na m1 m2 n1 r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m1
      n1 r0)
| Coq_prod_red_r (na, m2, n2, m1, r0) ->
  f21 _UU0393_ na m2 n2 m1 r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29
      (snoc _UU0393_ (Env.vass na m1)) m2 n2 r0)
| Coq_evar_red (ev, l, l', o) -> f22 _UU0393_ ev l l' o
| Coq_cast_red_l (m1, k, m2, n1, r0) ->
  f23 _UU0393_ m1 k m2 n1 r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m1
      n1 r0)
| Coq_cast_red_r (m2, k, n2, m1, r0) ->
  f24 _UU0393_ m2 k n2 m1 r0
    (red1_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
      f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _UU0393_ m2
      n2 r0)
| Coq_cast_red (m1, k, m2) -> f25 _UU0393_ m1 k m2
| Coq_fix_red_ty (mfix0, mfix1, idx, o) -> f26 _UU0393_ mfix0 mfix1 idx o
| Coq_fix_red_body (mfix0, mfix1, idx, o) -> f27 _UU0393_ mfix0 mfix1 idx o
| Coq_cofix_red_ty (mfix0, mfix1, idx, o) -> f28 _UU0393_ mfix0 mfix1 idx o
| Coq_cofix_red_body (mfix0, mfix1, idx, o) -> f29 _UU0393_ mfix0 mfix1 idx o

(** val red1_ind_all :
    Env.global_env -> (Env.context -> aname -> term -> term -> term -> term
    list -> 'a1) -> (Env.context -> aname -> term -> term -> term -> 'a1) ->
    (Env.context -> nat -> term -> __ -> 'a1) -> (Env.context -> case_info ->
    Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.constructor_body -> nat -> Instance.t -> term list -> term predicate
    -> term branch list -> term branch -> __ -> __ -> __ -> 'a1) ->
    (Env.context -> term mfixpoint -> nat -> term list -> nat -> term -> __
    -> __ -> 'a1) -> (Env.context -> case_info -> term predicate -> term
    mfixpoint -> nat -> term list -> nat -> term -> term branch list -> __ ->
    'a1) -> (Env.context -> projection -> term mfixpoint -> nat -> term list
    -> nat -> term -> __ -> 'a1) -> (Env.context -> kername ->
    Env.constant_body -> term -> __ -> Instance.t -> __ -> 'a1) ->
    (Env.context -> projection -> term list -> Instance.t -> term -> __ ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> red1 -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> term -> term -> red1 ->
    'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term -> term ->
    red1 -> 'a1 -> 'a1) -> (Env.context -> aname -> term -> term -> term ->
    term -> red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term list ->
    term list -> Instance.t -> aname list -> term -> term -> term branch list
    -> (term, (red1, 'a1) prod) coq_OnOne2 -> 'a1) -> (Env.context ->
    case_info -> Env.one_inductive_body -> Env.mutual_inductive_body -> __ ->
    term list -> Instance.t -> aname list -> term -> term -> term -> term
    branch list -> red1 -> 'a1 -> 'a1) -> (Env.context -> case_info -> term
    predicate -> term -> term -> term branch list -> red1 -> 'a1 -> 'a1) ->
    (Env.context -> case_info -> Env.mutual_inductive_body ->
    Env.one_inductive_body -> __ -> term predicate -> term -> term branch
    list -> term branch list -> (term branch, Env.context, ((red1, 'a1) prod,
    __) prod) coq_OnOne2All -> 'a1) -> (Env.context -> projection -> term ->
    term -> red1 -> 'a1 -> 'a1) -> (Env.context -> term -> term -> term list
    -> red1 -> 'a1 -> 'a1) -> (Env.context -> term list -> term list -> term
    -> (term, (red1, 'a1) prod) coq_OnOne2 -> 'a1) -> (Env.context -> aname
    -> term -> term -> term -> red1 -> 'a1 -> 'a1) -> (Env.context -> aname
    -> term -> term -> term -> red1 -> 'a1 -> 'a1) -> (Env.context -> nat ->
    term list -> term list -> (term, (red1, 'a1) prod) coq_OnOne2 -> 'a1) ->
    (Env.context -> term -> cast_kind -> term -> term -> red1 -> 'a1 -> 'a1)
    -> (Env.context -> term -> cast_kind -> term -> term -> red1 -> 'a1 ->
    'a1) -> (Env.context -> term -> cast_kind -> term -> 'a1) -> (Env.context
    -> term def list -> term def list -> nat -> (term def, ((red1, 'a1) prod,
    __) prod) coq_OnOne2 -> 'a1) -> (Env.context -> term def list -> term def
    list -> nat -> (term def, ((red1, 'a1) prod, __) prod) coq_OnOne2 -> 'a1)
    -> (Env.context -> term def list -> term def list -> nat -> (term def,
    ((red1, 'a1) prod, __) prod) coq_OnOne2 -> 'a1) -> (Env.context -> term
    def list -> term def list -> nat -> (term def, ((red1, 'a1) prod, __)
    prod) coq_OnOne2 -> 'a1) -> Env.context -> term -> term -> red1 -> 'a1 **)

let rec red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 _UU0393_ _ _ = function
| Coq_red_beta (na, t0, b, a, l) -> x _UU0393_ na t0 b a l
| Coq_red_zeta (na, b, t0, b') -> x0 _UU0393_ na b t0 b'
| Coq_red_rel (i, body) -> x1 _UU0393_ i body __
| Coq_red_iota (ci, mdecl, idecl, cdecl, c, u, args, p, brs, br) ->
  x2 _UU0393_ ci mdecl idecl cdecl c u args p brs br __ __ __
| Coq_red_fix (mfix, idx, args, narg, fn) ->
  x3 _UU0393_ mfix idx args narg fn __ __
| Coq_red_cofix_case (ip, p, mfix, idx, args, narg, fn, brs) ->
  x4 _UU0393_ ip p mfix idx args narg fn brs __
| Coq_red_cofix_proj (p, mfix, idx, args, narg, fn) ->
  x5 _UU0393_ p mfix idx args narg fn __
| Coq_red_delta (c, decl, body, u) -> x6 _UU0393_ c decl body __ u __
| Coq_red_proj (p, u, args, arg) -> x7 _UU0393_ p args u arg __
| Coq_abs_red_l (na, m, m', n, r) ->
  x8 _UU0393_ na m m' n r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ m m' r)
| Coq_abs_red_r (na, m, m', n, r) ->
  x9 _UU0393_ na m m' n r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      (snoc _UU0393_ (Env.vass na n)) m m' r)
| Coq_letin_red_def (na, b, t0, b', r, r0) ->
  x10 _UU0393_ na b t0 b' r r0
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ b r r0)
| Coq_letin_red_ty (na, b, t0, b', r, r0) ->
  x11 _UU0393_ na b t0 b' r r0
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ t0 r r0)
| Coq_letin_red_body (na, b, t0, b', r, r0) ->
  x12 _UU0393_ na b t0 b' r r0
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      (snoc _UU0393_ (Env.vdef na b t0)) b' r r0)
| Coq_case_red_pred_param (ind, params, params', puinst0, pcontext0,
                           preturn0, c, brs, o) ->
  x13 _UU0393_ ind params params' puinst0 pcontext0 preturn0 c brs
    (let rec auxl _ _ = function
     | OnOne2_hd (hd, hd', tl, r) ->
       OnOne2_hd (hd, hd', tl, (Coq_pair (r,
         (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
           x29 _UU0393_ hd hd' r))))
     | OnOne2_tl (hd, tl, tl', o1) ->
       OnOne2_tl (hd, tl, tl', (auxl tl tl' o1))
     in auxl params params' o)
| Coq_case_red_pred_return (ind, mdecl, idecl, params, puinst0, pcontext0,
                            preturn0, preturn', c, brs, x31) ->
  x14 _UU0393_ ind idecl mdecl __ params puinst0 pcontext0 preturn0 preturn'
    c brs x31
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      (Env.app_context _UU0393_
        (case_predicate_context ind.ci_ind mdecl idecl { puinst = puinst0;
          pparams = params; pcontext = pcontext0; preturn = preturn0 }))
      preturn0 preturn' x31)
| Coq_case_red_discr (ind, p, c, c', brs, r) ->
  x15 _UU0393_ ind p c c' brs r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ c c' r)
| Coq_case_red_brs (ind, mdecl, idecl, p, c, brs, brs', o) ->
  x16 _UU0393_ ind mdecl idecl __ p c brs brs'
    (let rec auxl _ _ _ = function
     | OnOne2All_hd (b, bs, hd, hd', tl, p0) ->
       OnOne2All_hd (b, bs, hd, hd', tl,
         (let Coq_pair (a, _) = p0 in
          Coq_pair ((Coq_pair (a,
          (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
            x29 (Env.app_context _UU0393_ b) hd.bbody hd'.bbody a))), __)))
     | OnOne2All_tl (b, bs, hd, tl, tl', o0) ->
       OnOne2All_tl (b, bs, hd, tl, tl', (auxl tl bs tl' o0))
     in auxl brs (case_branches_contexts ind.ci_ind mdecl idecl p brs) brs' o)
| Coq_proj_red (p, c, c', r) ->
  x17 _UU0393_ p c c' r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ c c' r)
| Coq_app_red_l (m1, n1, m2, r) ->
  x18 _UU0393_ m1 n1 m2 r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ m1 n1 r)
| Coq_app_red_r (m2, n2, m1, o) ->
  x19 _UU0393_ m2 n2 m1
    (let rec auxl _ _ = function
     | OnOne2_hd (hd, hd', tl, r) ->
       OnOne2_hd (hd, hd', tl, (Coq_pair (r,
         (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
           x29 _UU0393_ hd hd' r))))
     | OnOne2_tl (hd, tl, tl', o0) ->
       OnOne2_tl (hd, tl, tl', (auxl tl tl' o0))
     in auxl m2 n2 o)
| Coq_prod_red_l (na, m1, m2, n1, r) ->
  x20 _UU0393_ na m1 m2 n1 r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ m1 n1 r)
| Coq_prod_red_r (na, m2, n2, m1, r) ->
  x21 _UU0393_ na m2 n2 m1 r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      (snoc _UU0393_ (Env.vass na m1)) m2 n2 r)
| Coq_evar_red (ev, l, l', o) ->
  x22 _UU0393_ ev l l'
    (let rec auxl _ _ = function
     | OnOne2_hd (hd, hd', tl, r) ->
       OnOne2_hd (hd, hd', tl, (Coq_pair (r,
         (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
           x29 _UU0393_ hd hd' r))))
     | OnOne2_tl (hd, tl, tl', o0) ->
       OnOne2_tl (hd, tl, tl', (auxl tl tl' o0))
     in auxl l l' o)
| Coq_cast_red_l (m1, k, m2, n1, r) ->
  x23 _UU0393_ m1 k m2 n1 r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ m1 n1 r)
| Coq_cast_red_r (m2, k, n2, m1, r) ->
  x24 _UU0393_ m2 k n2 m1 r
    (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
      _UU0393_ m2 n2 r)
| Coq_cast_red (m1, k, m2) -> x25 _UU0393_ m1 k m2
| Coq_fix_red_ty (mfix0, mfix1, idx, o) ->
  x26 _UU0393_ mfix0 mfix1 idx
    (let rec auxl _ _ = function
     | OnOne2_hd (hd, hd', tl, p) ->
       OnOne2_hd (hd, hd', tl, (Coq_pair
         ((let Coq_pair (a, _) = p in
           Coq_pair (a,
           (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
             x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 _UU0393_ hd.dtype hd'.dtype a))), __)))
     | OnOne2_tl (hd, tl, tl', o0) ->
       OnOne2_tl (hd, tl, tl', (auxl tl tl' o0))
     in auxl mfix0 mfix1 o)
| Coq_fix_red_body (mfix0, mfix1, idx, o) ->
  x27 _UU0393_ mfix0 mfix1 idx
    (let c = fix_context mfix0 in
     let rec auxl _ _ = function
     | OnOne2_hd (hd, hd', tl, p) ->
       OnOne2_hd (hd, hd', tl, (Coq_pair
         ((let Coq_pair (a, _) = p in
           Coq_pair (a,
           (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
             x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 (Env.app_context _UU0393_ c) hd.dbody hd'.dbody a))), __)))
     | OnOne2_tl (hd, tl, tl', o0) ->
       OnOne2_tl (hd, tl, tl', (auxl tl tl' o0))
     in auxl mfix0 mfix1 o)
| Coq_cofix_red_ty (mfix0, mfix1, idx, o) ->
  x28 _UU0393_ mfix0 mfix1 idx
    (let rec auxl _ _ = function
     | OnOne2_hd (hd, hd', tl, p) ->
       OnOne2_hd (hd, hd', tl, (Coq_pair
         ((let Coq_pair (a, _) = p in
           Coq_pair (a,
           (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
             x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 _UU0393_ hd.dtype hd'.dtype a))), __)))
     | OnOne2_tl (hd, tl, tl', o0) ->
       OnOne2_tl (hd, tl, tl', (auxl tl tl' o0))
     in auxl mfix0 mfix1 o)
| Coq_cofix_red_body (mfix0, mfix1, idx, o) ->
  x29 _UU0393_ mfix0 mfix1 idx
    (let c = fix_context mfix0 in
     let rec auxl _ _ = function
     | OnOne2_hd (hd, hd', tl, p) ->
       OnOne2_hd (hd, hd', tl, (Coq_pair
         ((let Coq_pair (a, _) = p in
           Coq_pair (a,
           (red1_ind_all _UU03a3_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
             x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 (Env.app_context _UU0393_ c) hd.dbody hd'.dbody a))), __)))
     | OnOne2_tl (hd, tl, tl', o0) ->
       OnOne2_tl (hd, tl, tl', (auxl tl tl' o0))
     in auxl mfix0 mfix1 o)

type red =
| Coq_refl_red
| Coq_trans_red of term * term * red * red1

(** val red_rect :
    Env.global_env -> Env.context -> term -> 'a1 -> (term -> term -> red ->
    'a1 -> red1 -> 'a1) -> term -> red -> 'a1 **)

let rec red_rect _UU03a3_ _UU0393_ m f f0 _ = function
| Coq_refl_red -> f
| Coq_trans_red (p, n, r0, r1) ->
  f0 p n r0 (red_rect _UU03a3_ _UU0393_ m f f0 p r0) r1

(** val red_rec :
    Env.global_env -> Env.context -> term -> 'a1 -> (term -> term -> red ->
    'a1 -> red1 -> 'a1) -> term -> red -> 'a1 **)

let rec red_rec _UU03a3_ _UU0393_ m f f0 _ = function
| Coq_refl_red -> f
| Coq_trans_red (p, n, r0, r1) ->
  f0 p n r0 (red_rec _UU03a3_ _UU0393_ m f f0 p r0) r1

type eq_term_nocast = compare_term

type leq_term_nocast = compare_term

module Coq__1 = struct
 type cumul_gen =
 | Coq_cumul_refl of term * term * compare_term
 | Coq_cumul_red_l of term * term * term * red1 * cumul_gen
 | Coq_cumul_red_r of term * term * term * cumul_gen * red1
end
include Coq__1

(** val cumul_gen_rect :
    checker_flags -> Env.global_env_ext -> Env.context -> conv_pb -> (term ->
    term -> compare_term -> 'a1) -> (term -> term -> term -> red1 ->
    cumul_gen -> 'a1 -> 'a1) -> (term -> term -> term -> cumul_gen -> 'a1 ->
    red1 -> 'a1) -> term -> term -> cumul_gen -> 'a1 **)

let rec cumul_gen_rect h _UU03a3_ _UU0393_ pb f f0 f1 _ _ = function
| Coq_cumul_refl (t0, u, c0) -> f t0 u c0
| Coq_cumul_red_l (t0, u, v, r, c0) ->
  f0 t0 u v r c0 (cumul_gen_rect h _UU03a3_ _UU0393_ pb f f0 f1 v u c0)
| Coq_cumul_red_r (t0, u, v, c0, r) ->
  f1 t0 u v c0 (cumul_gen_rect h _UU03a3_ _UU0393_ pb f f0 f1 t0 v c0) r

(** val cumul_gen_rec :
    checker_flags -> Env.global_env_ext -> Env.context -> conv_pb -> (term ->
    term -> compare_term -> 'a1) -> (term -> term -> term -> red1 ->
    cumul_gen -> 'a1 -> 'a1) -> (term -> term -> term -> cumul_gen -> 'a1 ->
    red1 -> 'a1) -> term -> term -> cumul_gen -> 'a1 **)

let rec cumul_gen_rec h _UU03a3_ _UU0393_ pb f f0 f1 _ _ = function
| Coq_cumul_refl (t0, u, c0) -> f t0 u c0
| Coq_cumul_red_l (t0, u, v, r, c0) ->
  f0 t0 u v r c0 (cumul_gen_rec h _UU03a3_ _UU0393_ pb f f0 f1 v u c0)
| Coq_cumul_red_r (t0, u, v, c0, r) ->
  f1 t0 u v c0 (cumul_gen_rec h _UU03a3_ _UU0393_ pb f f0 f1 t0 v c0) r

(** val conv_refl' :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> cumul_gen **)

let conv_refl' h _UU03a3_ _ t0 =
  Coq_cumul_refl (t0, t0,
    (eq_term_refl h (Env.fst_ctx _UU03a3_) (global_ext_constraints _UU03a3_)
      t0))

(** val cumul_refl' :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> cumul_gen **)

let cumul_refl' h _UU03a3_ _ t0 =
  Coq_cumul_refl (t0, t0,
    (leq_term_refl h (Env.fst_ctx _UU03a3_) (global_ext_constraints _UU03a3_)
      t0))

type eq_opt_term = __

type eq_decl = (eq_opt_term, compare_term) prod

type eq_context = (term context_decl, term context_decl, eq_decl) coq_All2

module TemplateEnvTyping = EnvTyping(TemplateTerm)(Env)(TemplateTermUtils)

type 'typing coq_All_local_env = 'typing TemplateEnvTyping.coq_All_local_env =
| Coq_localenv_nil
| Coq_localenv_cons_abs of Env.context * aname * term
   * 'typing coq_All_local_env * 'typing
| Coq_localenv_cons_def of Env.context * aname * term * term
   * 'typing coq_All_local_env * 'typing * 'typing

(** val coq_All_local_env_rect :
    'a2 -> (Env.context -> aname -> term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (Env.context -> aname -> term -> term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> Env.context -> 'a1
    coq_All_local_env -> 'a2 **)

let rec coq_All_local_env_rect f f0 f1 _ = function
| Coq_localenv_nil -> f
| Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
  f0 _UU0393_ na t0 a0 (coq_All_local_env_rect f f0 f1 _UU0393_ a0) t1
| Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2) ->
  f1 _UU0393_ na b t0 a0 (coq_All_local_env_rect f f0 f1 _UU0393_ a0) t1 t2

(** val coq_All_local_env_rec :
    'a2 -> (Env.context -> aname -> term -> 'a1 coq_All_local_env -> 'a2 ->
    'a1 -> 'a2) -> (Env.context -> aname -> term -> term -> 'a1
    coq_All_local_env -> 'a2 -> 'a1 -> 'a1 -> 'a2) -> Env.context -> 'a1
    coq_All_local_env -> 'a2 **)

let rec coq_All_local_env_rec f f0 f1 _ = function
| Coq_localenv_nil -> f
| Coq_localenv_cons_abs (_UU0393_, na, t0, a0, t1) ->
  f0 _UU0393_ na t0 a0 (coq_All_local_env_rec f f0 f1 _UU0393_ a0) t1
| Coq_localenv_cons_def (_UU0393_, na, b, t0, a0, t1, t2) ->
  f1 _UU0393_ na b t0 a0 (coq_All_local_env_rec f f0 f1 _UU0393_ a0) t1 t2

type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

(** val coq_All_local_env_sig_pack :
    Env.context -> 'a1 coq_All_local_env -> Env.context * 'a1
    coq_All_local_env **)

let coq_All_local_env_sig_pack x all_local_env_var =
  x,all_local_env_var

(** val coq_All_local_env_Signature :
    Env.context -> ('a1 coq_All_local_env, Env.context, 'a1
    coq_All_local_env_sig) coq_Signature **)

let coq_All_local_env_Signature x all_local_env_var =
  x,all_local_env_var

(** val coq_NoConfusionPackage_All_local_env :
    (Env.context * 'a1 coq_All_local_env) coq_NoConfusionPackage **)

let coq_NoConfusionPackage_All_local_env =
  Build_NoConfusionPackage

(** val coq_All_local_env_fold :
    (nat -> term -> term) -> Env.context -> ('a1 coq_All_local_env, 'a1
    coq_All_local_env) iffT **)

let coq_All_local_env_fold =
  TemplateEnvTyping.coq_All_local_env_fold

(** val coq_All_local_env_impl :
    Env.context -> 'a1 coq_All_local_env -> (Env.context -> term ->
    Env.typ_or_sort -> 'a1 -> 'a2) -> 'a2 coq_All_local_env **)

let coq_All_local_env_impl =
  TemplateEnvTyping.coq_All_local_env_impl

(** val coq_All_local_env_impl_ind :
    Env.context -> 'a1 coq_All_local_env -> (Env.context -> term ->
    Env.typ_or_sort -> 'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2
    coq_All_local_env **)

let coq_All_local_env_impl_ind =
  TemplateEnvTyping.coq_All_local_env_impl_ind

(** val coq_All_local_env_skipn :
    Env.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env **)

let coq_All_local_env_skipn =
  TemplateEnvTyping.coq_All_local_env_skipn

type 'p coq_All_local_rel = 'p coq_All_local_env

(** val coq_All_local_rel_nil : Env.context -> 'a1 coq_All_local_rel **)

let coq_All_local_rel_nil _ =
  Coq_localenv_nil

(** val coq_All_local_rel_abs :
    Env.context -> Env.context -> term -> aname -> 'a1 coq_All_local_rel ->
    'a1 -> 'a1 coq_All_local_rel **)

let coq_All_local_rel_abs _ _UU0393_' a na x x0 =
  Coq_localenv_cons_abs (_UU0393_', na, a, x, x0)

(** val coq_All_local_rel_def :
    Env.context -> Env.context -> term -> term -> aname -> 'a1
    coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel **)

let coq_All_local_rel_def _ _UU0393_' t0 a na x x0 x1 =
  Coq_localenv_cons_def (_UU0393_', na, t0, a, x, x0, x1)

(** val coq_All_local_rel_local :
    Env.context -> 'a1 coq_All_local_env -> 'a1 coq_All_local_rel **)

let coq_All_local_rel_local _UU0393_ h =
  coq_All_local_env_impl _UU0393_ h (fun _ _ _ h' -> h')

(** val coq_All_local_local_rel :
    Env.context -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env **)

let coq_All_local_local_rel _UU0393_ x =
  coq_All_local_env_impl _UU0393_ x (fun _ _ _ xX -> xX)

(** val coq_All_local_app_rel :
    Env.context -> Env.context -> 'a1 coq_All_local_env -> ('a1
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
    Env.context -> Env.context -> 'a1 coq_All_local_env -> 'a1
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
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> Env.typ_or_sort -> ('a1, 'a2) lift_judgment -> (term ->
    'a1 -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment **)

let lift_judgment_impl =
  TemplateEnvTyping.lift_judgment_impl

type 'wf_term lift_wf_term =
  (('wf_term, 'wf_term) prod, 'wf_term) lift_judgment

type 'sorting infer_sort = (Universe.t, 'sorting) sigT

type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

type ('checking, 'sorting) lift_sorting =
  ('checking, 'sorting infer_sort) lift_judgment

type ('p, 'q) lift_typing2 = ('p, 'q) prod lift_typing

(** val infer_sort_impl :
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 ->
    'a2) -> 'a2 infer_sort **)

let infer_sort_impl =
  TemplateEnvTyping.infer_sort_impl

(** val infer_typing_sort_impl :
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 ->
    'a2) -> 'a2 infer_sort **)

let infer_typing_sort_impl =
  TemplateEnvTyping.infer_typing_sort_impl

(** val lift_typing_impl :
    Env.global_env_ext -> Env.global_env_ext -> Env.context -> Env.context ->
    term -> term -> Env.typ_or_sort -> 'a1 lift_typing -> (term -> 'a1 ->
    'a2) -> 'a2 lift_typing **)

let lift_typing_impl =
  TemplateEnvTyping.lift_typing_impl

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

(** val coq_All_local_env_over_gen_rect :
    Env.global_env_ext -> 'a5 -> (Env.context -> aname -> term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (Env.context -> aname -> term -> term -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> Env.context -> ('a1, 'a2) lift_judgment coq_All_local_env
    -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 **)

let rec coq_All_local_env_over_gen_rect _UU03a3_ f f0 f1 _ _ = function
| Coq_localenv_over_nil -> f
| Coq_localenv_over_cons_abs (_UU0393_, na, t0, all, a, tu, hs) ->
  f0 _UU0393_ na t0 all a
    (coq_All_local_env_over_gen_rect _UU03a3_ f f0 f1 _UU0393_ all a) tu hs
| Coq_localenv_over_cons_def (_UU0393_, na, b, t0, all, tb, a, hc, tu, hs) ->
  f1 _UU0393_ na b t0 all tb a
    (coq_All_local_env_over_gen_rect _UU03a3_ f f0 f1 _UU0393_ all a) hc tu hs

(** val coq_All_local_env_over_gen_rec :
    Env.global_env_ext -> 'a5 -> (Env.context -> aname -> term -> ('a1, 'a2)
    lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2) lift_judgment -> 'a4 ->
    'a5) -> (Env.context -> aname -> term -> term -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> 'a1 -> ('a1, 'a2, 'a3, 'a4)
    coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1, 'a2) lift_judgment ->
    'a4 -> 'a5) -> Env.context -> ('a1, 'a2) lift_judgment coq_All_local_env
    -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 **)

let rec coq_All_local_env_over_gen_rec _UU03a3_ f f0 f1 _ _ = function
| Coq_localenv_over_nil -> f
| Coq_localenv_over_cons_abs (_UU0393_, na, t0, all, a, tu, hs) ->
  f0 _UU0393_ na t0 all a
    (coq_All_local_env_over_gen_rec _UU03a3_ f f0 f1 _UU0393_ all a) tu hs
| Coq_localenv_over_cons_def (_UU0393_, na, b, t0, all, tb, a, hc, tu, hs) ->
  f1 _UU0393_ na b t0 all tb a
    (coq_All_local_env_over_gen_rec _UU03a3_ f f0 f1 _UU0393_ all a) hc tu hs

type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
  ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

(** val coq_All_local_env_over_gen_sig_pack :
    Env.global_env_ext -> Env.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen ->
    (Env.context * ('a1, 'a2) lift_judgment coq_All_local_env) * ('a1, 'a2,
    'a3, 'a4) coq_All_local_env_over_gen **)

let coq_All_local_env_over_gen_sig_pack _ _UU0393_ x all_local_env_over_gen_var =
  (_UU0393_,x),all_local_env_over_gen_var

(** val coq_All_local_env_over_gen_Signature :
    Env.global_env_ext -> Env.context -> ('a1, 'a2) lift_judgment
    coq_All_local_env -> (('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen,
    Env.context * ('a1, 'a2) lift_judgment coq_All_local_env, ('a1, 'a2, 'a3,
    'a4) coq_All_local_env_over_gen_sig) coq_Signature **)

let coq_All_local_env_over_gen_Signature _ _UU0393_ x all_local_env_over_gen_var =
  (_UU0393_,x),all_local_env_over_gen_var

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

(** val ctx_inst_rect :
    Env.global_env_ext -> Env.context -> 'a2 -> (aname -> term -> term ->
    term list -> Env.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> term -> term -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 **)

let rec ctx_inst_rect _UU03a3_ _UU0393_ f f0 f1 _ _ = function
| Coq_ctx_inst_nil -> f
| Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
  f0 na t0 i inst _UU0394_ t1 c
    (ctx_inst_rect _UU03a3_ _UU0393_ f f0 f1 inst
      (Env.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_) c)
| Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
  f1 na b t0 inst _UU0394_ c
    (ctx_inst_rect _UU03a3_ _UU0393_ f f0 f1 inst
      (Env.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_) c)

(** val ctx_inst_rec :
    Env.global_env_ext -> Env.context -> 'a2 -> (aname -> term -> term ->
    term list -> Env.context -> 'a1 -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname
    -> term -> term -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 ->
    'a2) -> term list -> Env.context -> 'a1 ctx_inst -> 'a2 **)

let rec ctx_inst_rec _UU03a3_ _UU0393_ f f0 f1 _ _ = function
| Coq_ctx_inst_nil -> f
| Coq_ctx_inst_ass (na, t0, i, inst, _UU0394_, t1, c) ->
  f0 na t0 i inst _UU0394_ t1 c
    (ctx_inst_rec _UU03a3_ _UU0393_ f f0 f1 inst
      (Env.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_) c)
| Coq_ctx_inst_def (na, b, t0, inst, _UU0394_, c) ->
  f1 na b t0 inst _UU0394_ c
    (ctx_inst_rec _UU03a3_ _UU0393_ f f0 f1 inst
      (Env.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_) c)

type 'typing ctx_inst_sig = 'typing ctx_inst

(** val ctx_inst_sig_pack :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
    ctx_inst -> (term list * Env.context) * 'a1 ctx_inst **)

let ctx_inst_sig_pack _ _ x x0 ctx_inst_var =
  (x,x0),ctx_inst_var

(** val ctx_inst_Signature :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> ('a1
    ctx_inst, term list * Env.context, 'a1 ctx_inst_sig) coq_Signature **)

let ctx_inst_Signature _ _ x x0 ctx_inst_var =
  (x,x0),ctx_inst_var

(** val coq_NoConfusionPackage_ctx_inst :
    Env.global_env_ext -> Env.context -> ((term list * Env.context) * 'a1
    ctx_inst) coq_NoConfusionPackage **)

let coq_NoConfusionPackage_ctx_inst _ _ =
  Build_NoConfusionPackage

(** val ctx_inst_impl_gen :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> __ list
    -> (__, __ ctx_inst) sigT -> (term -> term -> (__, __) coq_All -> 'a1) ->
    (__, __ ctx_inst) coq_All -> 'a1 ctx_inst **)

let ctx_inst_impl_gen =
  TemplateEnvTyping.ctx_inst_impl_gen

(** val ctx_inst_impl :
    Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
    ctx_inst -> (term -> term -> 'a1 -> 'a2) -> 'a2 ctx_inst **)

let ctx_inst_impl =
  TemplateEnvTyping.ctx_inst_impl

(** val coq_All_local_env_size_gen :
    (Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> 'a1 ->
    size) -> size -> Env.global_env_ext -> Env.context -> 'a1
    coq_All_local_env -> size **)

let rec coq_All_local_env_size_gen psize base _UU03a3_ _ = function
| Coq_localenv_nil -> base
| Coq_localenv_cons_abs (_UU0393_', _, t0, w', p) ->
  Nat.add (psize _UU03a3_ _UU0393_' t0 Sort p)
    (coq_All_local_env_size_gen psize base _UU03a3_ _UU0393_' w')
| Coq_localenv_cons_def (_UU0393_', _, b, t0, w', pt, pb) ->
  Nat.add
    (Nat.add (psize _UU03a3_ _UU0393_' t0 Sort pt)
      (psize _UU03a3_ _UU0393_' b (Typ t0) pb))
    (coq_All_local_env_size_gen psize base _UU03a3_ _UU0393_' w')

(** val lift_judgment_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> 'a2 -> size) ->
    Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1,
    'a2) lift_judgment -> size **)

let lift_judgment_size csize ssize _UU03a3_ _UU0393_ t0 t1 w =
  match t1 with
  | Typ t2 -> Obj.magic csize _UU03a3_ _UU0393_ t0 t2 w
  | Sort -> Obj.magic ssize _UU03a3_ _UU0393_ t0 w

(** val lift_typing_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1, 'a1
    infer_sort) lift_judgment -> size **)

let lift_typing_size typing_size0 =
  lift_judgment_size typing_size0 (fun _UU03a3_ _UU0393_ t0 tu ->
    let Coq_existT (s, d) = tu in
    typing_size0 _UU03a3_ _UU0393_ t0 (Coq_tSort s) d)

(** val coq_All_local_env_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    Env.global_env_ext -> Env.context -> ('a1, 'a1 infer_sort) lift_judgment
    coq_All_local_env -> size **)

let coq_All_local_env_size typing_size0 =
  coq_All_local_env_size_gen (lift_typing_size typing_size0) O

(** val coq_All_local_rel_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    Env.global_env_ext -> Env.context -> Env.context -> ('a1, 'a1 infer_sort)
    lift_judgment coq_All_local_rel -> size **)

let coq_All_local_rel_size typing_size0 _UU03a3_ _UU0393_ _UU0394_ w =
  coq_All_local_env_size_gen (fun _UU03a3_0 _UU0394_0 ->
    lift_typing_size typing_size0 _UU03a3_0
      (Env.app_context _UU0393_ _UU0394_0)) O _UU03a3_ _UU0394_ w

(** val lift_sorting_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size)
    -> Env.global_env_ext -> Env.context -> term -> Env.typ_or_sort -> ('a1,
    'a2 infer_sort) lift_judgment -> size **)

let lift_sorting_size checking_size sorting_size =
  lift_judgment_size checking_size (fun _UU03a3_ _UU0393_ t0 tu ->
    let Coq_existT (s, d) = tu in sorting_size _UU03a3_ _UU0393_ t0 s d)

(** val coq_All_local_env_sorting_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size)
    -> Env.global_env_ext -> Env.context -> ('a1, 'a2 infer_sort)
    lift_judgment coq_All_local_env -> size **)

let coq_All_local_env_sorting_size checking_size sorting_size =
  coq_All_local_env_size_gen (lift_sorting_size checking_size sorting_size)
    (S O)

(** val coq_All_local_rel_sorting_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    (Env.global_env_ext -> Env.context -> term -> Universe.t -> 'a2 -> size)
    -> Env.global_env_ext -> Env.context -> Env.context -> ('a1, 'a2
    infer_sort) lift_judgment coq_All_local_rel -> size **)

let coq_All_local_rel_sorting_size checking_size sorting_size _UU03a3_ _UU0393_ _UU0394_ w =
  coq_All_local_env_size_gen (fun _UU03a3_0 _UU0394_0 ->
    lift_sorting_size checking_size sorting_size _UU03a3_0
      (Env.app_context _UU0393_ _UU0394_0)) (S O) _UU03a3_ _UU0394_ w

module TemplateConversion =
 Conversion(TemplateTerm)(Env)(TemplateTermUtils)(TemplateEnvTyping)

type 'p coq_All_decls_alpha_pb = 'p TemplateConversion.coq_All_decls_alpha_pb =
| Coq_all_decls_alpha_vass of name binder_annot * name binder_annot * 
   term * term * 'p
| Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot * 
   term * term * term * term * 'p * 'p

(** val coq_All_decls_alpha_pb_rect :
    conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __
    -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2 **)

let coq_All_decls_alpha_pb_rect _ f f0 _ _ = function
| Coq_all_decls_alpha_vass (na, na', t0, t', eqt) -> f na na' t0 t' __ eqt
| Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb0, eqt) ->
  f0 na na' b t0 b' t' __ eqb0 eqt

(** val coq_All_decls_alpha_pb_rec :
    conv_pb -> (name binder_annot -> name binder_annot -> term -> term -> __
    -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term context_decl -> term
    context_decl -> 'a1 coq_All_decls_alpha_pb -> 'a2 **)

let coq_All_decls_alpha_pb_rec _ f f0 _ _ = function
| Coq_all_decls_alpha_vass (na, na', t0, t', eqt) -> f na na' t0 t' __ eqt
| Coq_all_decls_alpha_vdef (na, na', b, t0, b', t', eqb0, eqt) ->
  f0 na na' b t0 b' t' __ eqb0 eqt

type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

(** val coq_All_decls_alpha_pb_sig_pack :
    conv_pb -> term context_decl -> term context_decl -> 'a1
    coq_All_decls_alpha_pb -> (term context_decl * term context_decl) * 'a1
    coq_All_decls_alpha_pb **)

let coq_All_decls_alpha_pb_sig_pack _ x x0 all_decls_alpha_pb_var =
  (x,x0),all_decls_alpha_pb_var

(** val coq_All_decls_alpha_pb_Signature :
    conv_pb -> term context_decl -> term context_decl -> ('a1
    coq_All_decls_alpha_pb, term context_decl * term context_decl, 'a1
    coq_All_decls_alpha_pb_sig) coq_Signature **)

let coq_All_decls_alpha_pb_Signature _ x x0 all_decls_alpha_pb_var =
  (x,x0),all_decls_alpha_pb_var

(** val coq_NoConfusionPackage_All_decls_alpha_pb :
    conv_pb -> ((term context_decl * term context_decl) * 'a1
    coq_All_decls_alpha_pb) coq_NoConfusionPackage **)

let coq_NoConfusionPackage_All_decls_alpha_pb _ =
  Build_NoConfusionPackage

type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

type 'cumul_gen cumul_pb_context =
  (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

type 'cumul_gen cumul_ctx_rel =
  (term context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

(** val coq_All_decls_alpha_pb_impl :
    conv_pb -> term context_decl -> term context_decl -> (conv_pb -> term ->
    term -> 'a1 -> 'a2) -> 'a1 coq_All_decls_alpha_pb -> 'a2
    coq_All_decls_alpha_pb **)

let coq_All_decls_alpha_pb_impl =
  TemplateConversion.coq_All_decls_alpha_pb_impl

module TemplateGlobalMaps =
 GlobalMaps(TemplateTerm)(Env)(TemplateTermUtils)(TemplateEnvTyping)(TemplateConversion)(TemplateLookup)

type 'p on_context = 'p TemplateEnvTyping.coq_All_local_env

type 'p type_local_ctx = __

type 'p sorts_local_ctx = __

type 'p on_type = 'p

(** val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t **)

let univs_ext_constraints univs _UU03c6_ =
  ConstraintSet.union (constraints_of_udecl _UU03c6_) univs

(** val ind_realargs : Env.one_inductive_body -> nat **)

let ind_realargs o =
  match destArity Coq_nil (Env.ind_type o) with
  | Some p ->
    let Coq_pair (ctx, _) = p in length (Env.smash_context Coq_nil ctx)
  | None -> O

type positive_cstr_arg = TemplateGlobalMaps.positive_cstr_arg =
| Coq_pos_arg_closed of term
| Coq_pos_arg_concl of term list * nat * Env.one_inductive_body
   * (term, __) coq_All
| Coq_pos_arg_let of aname * term * term * term * positive_cstr_arg
| Coq_pos_arg_ass of aname * term * term * positive_cstr_arg

(** val positive_cstr_arg_rect :
    Env.mutual_inductive_body -> (term context_decl list -> term -> __ ->
    'a1) -> (term context_decl list -> term list -> nat ->
    Env.one_inductive_body -> __ -> (term, __) coq_All -> __ -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> term -> positive_cstr_arg
    -> 'a1 -> 'a1) -> (term context_decl list -> aname -> term -> term -> __
    -> positive_cstr_arg -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr_arg -> 'a1 **)

let rec positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_ _ = function
| Coq_pos_arg_closed ty -> f _UU0393_ ty __
| Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
| Coq_pos_arg_let (na, b, ty, ty', p0) ->
  f1 _UU0393_ na b ty ty' p0
    (positive_cstr_arg_rect mdecl f f0 f1 f2 _UU0393_
      (subst (Coq_cons (b, Coq_nil)) O ty') p0)
| Coq_pos_arg_ass (na, ty, ty', p0) ->
  f2 _UU0393_ na ty ty' __ p0
    (positive_cstr_arg_rect mdecl f f0 f1 f2 (Coq_cons ((Env.vass na ty),
      _UU0393_)) ty' p0)

(** val positive_cstr_arg_rec :
    Env.mutual_inductive_body -> (term context_decl list -> term -> __ ->
    'a1) -> (term context_decl list -> term list -> nat ->
    Env.one_inductive_body -> __ -> (term, __) coq_All -> __ -> 'a1) -> (term
    context_decl list -> aname -> term -> term -> term -> positive_cstr_arg
    -> 'a1 -> 'a1) -> (term context_decl list -> aname -> term -> term -> __
    -> positive_cstr_arg -> 'a1 -> 'a1) -> term context_decl list -> term ->
    positive_cstr_arg -> 'a1 **)

let rec positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_ _ = function
| Coq_pos_arg_closed ty -> f _UU0393_ ty __
| Coq_pos_arg_concl (l, k, i, a) -> f0 _UU0393_ l k i __ a __
| Coq_pos_arg_let (na, b, ty, ty', p0) ->
  f1 _UU0393_ na b ty ty' p0
    (positive_cstr_arg_rec mdecl f f0 f1 f2 _UU0393_
      (subst (Coq_cons (b, Coq_nil)) O ty') p0)
| Coq_pos_arg_ass (na, ty, ty', p0) ->
  f2 _UU0393_ na ty ty' __ p0
    (positive_cstr_arg_rec mdecl f f0 f1 f2 (Coq_cons ((Env.vass na ty),
      _UU0393_)) ty' p0)

type positive_cstr = TemplateGlobalMaps.positive_cstr =
| Coq_pos_concl of term list * (term, __) coq_All
| Coq_pos_let of aname * term * term * term * positive_cstr
| Coq_pos_ass of aname * term * term * positive_cstr_arg * positive_cstr

(** val positive_cstr_rect :
    Env.mutual_inductive_body -> nat -> (term context_decl list -> term list
    -> (term, __) coq_All -> 'a1) -> (term context_decl list -> aname -> term
    -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term context_decl
    list -> aname -> term -> term -> positive_cstr_arg -> positive_cstr ->
    'a1 -> 'a1) -> term context_decl list -> term -> positive_cstr -> 'a1 **)

let rec positive_cstr_rect mdecl i f f0 f1 _UU0393_ _ = function
| Coq_pos_concl (l, x) -> f _UU0393_ l x
| Coq_pos_let (na, b, ty, ty', p0) ->
  f0 _UU0393_ na b ty ty' p0
    (positive_cstr_rect mdecl i f f0 f1 _UU0393_
      (subst (Coq_cons (b, Coq_nil)) O ty') p0)
| Coq_pos_ass (na, ty, ty', p0, p1) ->
  f1 _UU0393_ na ty ty' p0 p1
    (positive_cstr_rect mdecl i f f0 f1 (Coq_cons ((Env.vass na ty),
      _UU0393_)) ty' p1)

(** val positive_cstr_rec :
    Env.mutual_inductive_body -> nat -> (term context_decl list -> term list
    -> (term, __) coq_All -> 'a1) -> (term context_decl list -> aname -> term
    -> term -> term -> positive_cstr -> 'a1 -> 'a1) -> (term context_decl
    list -> aname -> term -> term -> positive_cstr_arg -> positive_cstr ->
    'a1 -> 'a1) -> term context_decl list -> term -> positive_cstr -> 'a1 **)

let rec positive_cstr_rec mdecl i f f0 f1 _UU0393_ _ = function
| Coq_pos_concl (l, x) -> f _UU0393_ l x
| Coq_pos_let (na, b, ty, ty', p0) ->
  f0 _UU0393_ na b ty ty' p0
    (positive_cstr_rec mdecl i f f0 f1 _UU0393_
      (subst (Coq_cons (b, Coq_nil)) O ty') p0)
| Coq_pos_ass (na, ty, ty', p0, p1) ->
  f1 _UU0393_ na ty ty' p0 p1
    (positive_cstr_rec mdecl i f f0 f1 (Coq_cons ((Env.vass na ty),
      _UU0393_)) ty' p1)

(** val lift_level : nat -> Level.t_ -> Level.t_ **)

let lift_level n l = match l with
| Level.Coq_lvar k -> Level.Coq_lvar (Nat.add n k)
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
             ConstraintSet.add (Coq_pair ((Coq_pair (u0, ConstraintType.Eq)),
               u'0)) (variance_cstrs vs us us'))))

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

(** val ind_arities : Env.mutual_inductive_body -> term context_decl list **)

let ind_arities mdecl =
  Env.arities_context (Env.ind_bodies mdecl)

type 'pcmp ind_respects_variance = __

type 'pcmp cstr_respects_variance = __

(** val cstr_concl_head :
    Env.mutual_inductive_body -> nat -> Env.constructor_body -> term **)

let cstr_concl_head mdecl i cdecl =
  Coq_tRel
    (Nat.add
      (Nat.add (Nat.sub (length (Env.ind_bodies mdecl)) (S i))
        (length (Env.ind_params mdecl))) (length (Env.cstr_args cdecl)))

(** val cstr_concl :
    Env.mutual_inductive_body -> nat -> Env.constructor_body -> term **)

let cstr_concl mdecl i cdecl =
  mkApps (cstr_concl_head mdecl i cdecl)
    (app
      (Env.to_extended_list_k (Env.ind_params mdecl)
        (length (Env.cstr_args cdecl))) (Env.cstr_indices cdecl))

type ('pcmp, 'p) on_constructor = ('pcmp, 'p) TemplateGlobalMaps.on_constructor = { 
on_ctype : 'p on_type; on_cargs : 'p sorts_local_ctx;
on_cindices : 'p TemplateEnvTyping.ctx_inst;
on_ctype_positive : positive_cstr;
on_ctype_variance : (Variance.t list -> __ -> 'pcmp cstr_respects_variance) }

(** val on_ctype :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> 'a2 on_type **)

let on_ctype _ _ _ _ _ _ _ _ o =
  o.on_ctype

(** val on_cargs :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> 'a2 sorts_local_ctx **)

let on_cargs _ _ _ _ _ _ _ _ o =
  o.on_cargs

(** val on_cindices :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> 'a2
    TemplateEnvTyping.ctx_inst **)

let on_cindices _ _ _ _ _ _ _ _ o =
  o.on_cindices

(** val on_ctype_positive :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> positive_cstr **)

let on_ctype_positive _ _ _ _ _ _ _ _ o =
  o.on_ctype_positive

(** val on_ctype_variance :
    checker_flags -> Env.global_env_ext -> Env.mutual_inductive_body -> nat
    -> Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ('a1, 'a2) on_constructor -> Variance.t list -> 'a1
    cstr_respects_variance **)

let on_ctype_variance _ _ _ _ _ _ _ _ o v =
  o.on_ctype_variance v __

type ('pcmp, 'p) on_constructors =
  (Env.constructor_body, Universe.t list, ('pcmp, 'p) on_constructor) coq_All2

type on_projections =
  (Env.projection_body, __) coq_Alli
  (* singleton inductive, whose constructor was Build_on_projections *)

(** val on_projs :
    Env.mutual_inductive_body -> kername -> nat -> Env.one_inductive_body ->
    Env.context -> Env.constructor_body -> on_projections ->
    (Env.projection_body, __) coq_Alli **)

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

type ('pcmp, 'p) on_ind_body = ('pcmp, 'p) TemplateGlobalMaps.on_ind_body = { 
onArity : 'p on_type; ind_cunivs : constructor_univs list;
onConstructors : ('pcmp, 'p) on_constructors; onProjections : __;
ind_sorts : 'p check_ind_sorts; onIndices : __ }

(** val onArity :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> 'a2 on_type **)

let onArity _ _ _ _ _ _ o =
  o.onArity

(** val ind_cunivs :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> constructor_univs list **)

let ind_cunivs _ _ _ _ _ _ o =
  o.ind_cunivs

(** val onConstructors :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> ('a1, 'a2) on_constructors **)

let onConstructors _ _ _ _ _ _ o =
  o.onConstructors

(** val onProjections :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> __ **)

let onProjections _ _ _ _ _ _ o =
  o.onProjections

(** val ind_sorts :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> 'a2 check_ind_sorts **)

let ind_sorts _ _ _ _ _ _ o =
  o.ind_sorts

(** val onIndices :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> nat -> Env.one_inductive_body -> ('a1, 'a2)
    on_ind_body -> __ **)

let onIndices _ _ _ _ _ _ o =
  o.onIndices

type on_variance = __

type ('pcmp, 'p) on_inductive = ('pcmp, 'p) TemplateGlobalMaps.on_inductive = { 
onInductives : (Env.one_inductive_body, ('pcmp, 'p) on_ind_body) coq_Alli;
onParams : 'p on_context; onVariance : on_variance }

(** val onInductives :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    (Env.one_inductive_body, ('a1, 'a2) on_ind_body) coq_Alli **)

let onInductives _ _ _ _ o =
  o.onInductives

(** val onParams :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> ('a1, 'a2) on_inductive -> 'a2 on_context **)

let onParams _ _ _ _ o =
  o.onParams

(** val onVariance :
    checker_flags -> Env.global_env_ext -> kername ->
    Env.mutual_inductive_body -> ('a1, 'a2) on_inductive -> on_variance **)

let onVariance _ _ _ _ o =
  o.onVariance

type 'p on_constant_decl = __

type ('pcmp, 'p) on_global_decl = __

type ('pcmp, 'p) on_global_decls_data =
  ('pcmp, 'p) on_global_decl
  (* singleton inductive, whose constructor was Build_on_global_decls_data *)

(** val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls_data -> universes_decl **)

let udecl _ _ _ _ _ d _ =
  TemplateLookup.universes_decl_of_decl d

(** val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls_data -> ('a1, 'a2) on_global_decl **)

let on_global_decl_d _ _ _ _ _ _ o =
  o

type ('pcmp, 'p) on_global_decls = ('pcmp, 'p) TemplateGlobalMaps.on_global_decls =
| Coq_globenv_nil
| Coq_globenv_decl of Env.global_declarations * kername * Env.global_decl
   * ('pcmp, 'p) on_global_decls * ('pcmp, 'p) on_global_decls_data

(** val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    Env.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

let rec on_global_decls_rect cf univs retro f f0 _ = function
| Coq_globenv_nil -> f
| Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
  f0 _UU03a3_ kn d o0 (on_global_decls_rect cf univs retro f f0 _UU03a3_ o0)
    o1

(** val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (Env.global_declarations -> kername -> Env.global_decl -> ('a1, 'a2)
    on_global_decls -> 'a3 -> ('a1, 'a2) on_global_decls_data -> 'a3) ->
    Env.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3 **)

let rec on_global_decls_rec cf univs retro f f0 _ = function
| Coq_globenv_nil -> f
| Coq_globenv_decl (_UU03a3_, kn, d, o0, o1) ->
  f0 _UU03a3_ kn d o0 (on_global_decls_rec cf univs retro f f0 _UU03a3_ o0) o1

type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

(** val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> ('a1, 'a2) on_global_decls ->
    Env.global_declarations * ('a1, 'a2) on_global_decls **)

let on_global_decls_sig_pack _ _ _ x on_global_decls_var =
  x,on_global_decls_var

(** val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    Env.global_declarations -> (('a1, 'a2) on_global_decls,
    Env.global_declarations, ('a1, 'a2) on_global_decls_sig) coq_Signature **)

let on_global_decls_Signature _ _ _ x on_global_decls_var =
  x,on_global_decls_var

type ('pcmp, 'p) on_global_env = (__, ('pcmp, 'p) on_global_decls) prod

type ('pcmp, 'p) on_global_env_ext = (('pcmp, 'p) on_global_env, __) prod

(** val type_local_ctx_impl_gen :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t -> __ list
    -> (__, __ type_local_ctx) sigT -> (Env.context -> term ->
    Env.typ_or_sort -> (__, __) coq_All -> 'a1) -> (__, __ type_local_ctx)
    coq_All -> 'a1 type_local_ctx **)

let type_local_ctx_impl_gen =
  TemplateGlobalMaps.type_local_ctx_impl_gen

(** val type_local_ctx_impl :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t -> 'a1
    type_local_ctx -> (Env.context -> term -> Env.typ_or_sort -> 'a1 -> 'a2)
    -> 'a2 type_local_ctx **)

let type_local_ctx_impl =
  TemplateGlobalMaps.type_local_ctx_impl

(** val sorts_local_ctx_impl_gen :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t list -> __
    list -> (__, __ sorts_local_ctx) sigT -> (Env.context -> term ->
    Env.typ_or_sort -> (__, __) coq_All -> 'a1) -> (__, __ sorts_local_ctx)
    coq_All -> 'a1 sorts_local_ctx **)

let sorts_local_ctx_impl_gen =
  TemplateGlobalMaps.sorts_local_ctx_impl_gen

(** val sorts_local_ctx_impl :
    Env.global_env_ext -> Env.context -> Env.context -> Universe.t list ->
    'a1 sorts_local_ctx -> (Env.context -> term -> Env.typ_or_sort -> 'a1 ->
    'a2) -> 'a2 sorts_local_ctx **)

let sorts_local_ctx_impl =
  TemplateGlobalMaps.sorts_local_ctx_impl

(** val cstr_respects_variance_impl_gen :
    Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
    Env.constructor_body -> __ list -> (__, __ cstr_respects_variance) sigT
    -> __ -> (__, __ cstr_respects_variance) coq_All -> 'a1
    cstr_respects_variance **)

let cstr_respects_variance_impl_gen =
  TemplateGlobalMaps.cstr_respects_variance_impl_gen

(** val cstr_respects_variance_impl :
    Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
    Env.constructor_body -> __ -> 'a2 cstr_respects_variance -> 'a1
    cstr_respects_variance **)

let cstr_respects_variance_impl =
  TemplateGlobalMaps.cstr_respects_variance_impl

(** val on_constructor_impl_config_gen :
    Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
    Env.one_inductive_body -> Env.context -> Env.constructor_body ->
    Universe.t list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (Env.context -> term -> Env.typ_or_sort -> (((checker_flags, __) prod,
    __) prod, __) coq_All -> 'a2) -> (universes_decl -> Env.context -> term
    -> term -> conv_pb -> (((checker_flags, __) prod, __) prod, __) coq_All
    -> 'a1) -> (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1,
    'a2) on_constructor **)

let on_constructor_impl_config_gen =
  TemplateGlobalMaps.on_constructor_impl_config_gen

(** val on_constructors_impl_config_gen :
    Env.global_env_ext -> Env.mutual_inductive_body -> nat ->
    Env.one_inductive_body -> Env.context -> Env.constructor_body list ->
    Universe.t list list -> ((checker_flags, __) prod, __) prod list ->
    checker_flags -> (((checker_flags, __) prod, __) prod, __) sigT ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> (Env.context -> term
    -> Env.typ_or_sort -> (((checker_flags, __) prod, __) prod, __) coq_All
    -> 'a2) -> (universes_decl -> Env.context -> term -> term -> conv_pb ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> 'a1) ->
    (((checker_flags, __) prod, __) prod, __) coq_All -> ('a1, 'a2)
    on_constructors **)

let on_constructors_impl_config_gen =
  TemplateGlobalMaps.on_constructors_impl_config_gen

(** val ind_respects_variance_impl :
    Env.global_env -> Env.mutual_inductive_body -> Variance.t list ->
    Env.context -> __ -> 'a1 ind_respects_variance -> 'a2
    ind_respects_variance **)

let ind_respects_variance_impl =
  TemplateGlobalMaps.ind_respects_variance_impl

(** val on_variance_impl :
    Env.global_env -> universes_decl -> Variance.t list option ->
    checker_flags -> checker_flags -> on_variance -> on_variance **)

let on_variance_impl =
  TemplateGlobalMaps.on_variance_impl

(** val on_global_env_impl_config :
    checker_flags -> checker_flags -> ((Env.global_env, universes_decl) prod
    -> Env.context -> term -> Env.typ_or_sort -> ('a1, 'a3) on_global_env ->
    ('a2, 'a4) on_global_env -> 'a3 -> 'a4) -> ((Env.global_env,
    universes_decl) prod -> Env.context -> term -> term -> conv_pb -> ('a1,
    'a3) on_global_env -> ('a2, 'a4) on_global_env -> 'a1 -> 'a2) ->
    Env.global_env -> ('a1, 'a3) on_global_env -> ('a2, 'a4) on_global_env **)

let on_global_env_impl_config =
  TemplateGlobalMaps.on_global_env_impl_config

(** val on_global_env_impl :
    checker_flags -> ((Env.global_env, universes_decl) prod -> Env.context ->
    term -> Env.typ_or_sort -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env -> 'a2 -> 'a3) -> Env.global_env -> ('a1, 'a2)
    on_global_env -> ('a1, 'a3) on_global_env **)

let on_global_env_impl =
  TemplateGlobalMaps.on_global_env_impl

module TemplateConversionPar =
 struct
  type cumul_gen = Coq__1.cumul_gen
 end

type coq_GuardChecker = { fix_guard : (Env.global_env_ext -> Env.context ->
                                      term mfixpoint -> bool);
                          cofix_guard : (Env.global_env_ext -> Env.context ->
                                        term mfixpoint -> bool) }

(** val fix_guard :
    coq_GuardChecker -> Env.global_env_ext -> Env.context -> term mfixpoint
    -> bool **)

let fix_guard guardChecker =
  guardChecker.fix_guard

(** val cofix_guard :
    coq_GuardChecker -> Env.global_env_ext -> Env.context -> term mfixpoint
    -> bool **)

let cofix_guard guardChecker =
  guardChecker.cofix_guard

(** val guard_checking : coq_GuardChecker **)

let guard_checking =
  failwith "AXIOM TO BE REALIZED"

(** val destInd : term -> (inductive, Instance.t) prod option **)

let destInd = function
| Coq_tInd (ind, u) -> Some (Coq_pair (ind, u))
| _ -> None

(** val isFinite : recursivity_kind -> bool **)

let isFinite = function
| Finite -> Coq_true
| _ -> Coq_false

(** val isCoFinite : recursivity_kind -> bool **)

let isCoFinite = function
| CoFinite -> Coq_true
| _ -> Coq_false

(** val check_recursivity_kind :
    Env.global_env -> kername -> recursivity_kind -> bool **)

let check_recursivity_kind _UU03a3_ ind r =
  match Env.lookup_env _UU03a3_ ind with
  | Some g ->
    (match g with
     | Env.ConstantDecl _ -> Coq_false
     | Env.InductiveDecl mib ->
       eqb reflect_recursivity_kind (Env.ind_finite mib) r)
  | None -> Coq_false

(** val check_one_fix : term def -> kername option **)

let check_one_fix d =
  let { dname = _; dtype = ty; dbody = _; rarg = arg } = d in
  let Coq_pair (ctx, _) = decompose_prod_assum Coq_nil ty in
  (match nth_error (List.rev (Env.smash_context Coq_nil ctx)) arg with
   | Some argd ->
     let Coq_pair (hd, _) = decompose_app argd.decl_type in
     (match destInd hd with
      | Some p ->
        let Coq_pair (i, _) = p in
        let { inductive_mind = mind; inductive_ind = _ } = i in Some mind
      | None -> None)
   | None -> None)

(** val wf_fixpoint : Env.global_env -> term def list -> bool **)

let wf_fixpoint _UU03a3_ mfix =
  match forallb (let f0 = fun d -> d.dbody in fun x -> isLambda (f0 x)) mfix with
  | Coq_true ->
    let checks = map check_one_fix mfix in
    (match map_option_out checks with
     | Some l ->
       (match l with
        | Coq_nil -> Coq_false
        | Coq_cons (ind, inds0) ->
          (match forallb (eqb Kername.reflect_kername ind) inds0 with
           | Coq_true -> check_recursivity_kind _UU03a3_ ind Finite
           | Coq_false -> Coq_false))
     | None -> Coq_false)
  | Coq_false -> Coq_false

(** val check_one_cofix : term def -> kername option **)

let check_one_cofix d =
  let { dname = _; dtype = ty; dbody = _; rarg = _ } = d in
  let Coq_pair (_, ty0) = decompose_prod_assum Coq_nil ty in
  let Coq_pair (hd, _) = decompose_app ty0 in
  (match destInd hd with
   | Some p ->
     let Coq_pair (i, _) = p in
     let { inductive_mind = ind; inductive_ind = _ } = i in Some ind
   | None -> None)

(** val wf_cofixpoint : Env.global_env -> term def list -> bool **)

let wf_cofixpoint _UU03a3_ mfix =
  let checks = map check_one_cofix mfix in
  (match map_option_out checks with
   | Some l ->
     (match l with
      | Coq_nil -> Coq_false
      | Coq_cons (ind, inds0) ->
        (match forallb (eqb Kername.reflect_kername ind) inds0 with
         | Coq_true -> check_recursivity_kind _UU03a3_ ind CoFinite
         | Coq_false -> Coq_false))
   | None -> Coq_false)

module Coq__2 = struct
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
include Coq__2

(** val typing_rect :
    checker_flags -> Env.global_env_ext -> (Env.context -> nat -> term
    context_decl -> typing lift_typing coq_All_local_env -> __ -> 'a1) ->
    (Env.context -> Universe.t -> typing lift_typing coq_All_local_env -> __
    -> 'a1) -> (Env.context -> term -> cast_kind -> term -> Universe.t ->
    typing -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term
    -> term -> Universe.t -> Universe.t -> typing -> 'a1 -> typing -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> Universe.t -> term ->
    typing -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term
    -> term -> term -> Universe.t -> term -> typing -> 'a1 -> typing -> 'a1
    -> typing -> 'a1 -> 'a1) -> (Env.context -> term -> term list -> term ->
    term -> typing -> 'a1 -> __ -> __ -> typing_spine -> 'a1) -> (Env.context
    -> kername -> Instance.t -> typing lift_typing coq_All_local_env ->
    Env.constant_body -> __ -> __ -> 'a1) -> (Env.context -> inductive ->
    Instance.t -> typing lift_typing coq_All_local_env ->
    Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> __ -> 'a1)
    -> (Env.context -> inductive -> nat -> Instance.t -> typing lift_typing
    coq_All_local_env -> Env.mutual_inductive_body -> Env.one_inductive_body
    -> Env.constructor_body -> __ -> __ -> 'a1) -> (Env.context -> case_info
    -> term predicate -> term -> term branch list -> term list -> Universe.t
    -> Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> __ ->
    (name binder_annot, term context_decl, __) coq_All2 -> __ -> __ -> typing
    ctx_inst -> typing -> 'a1 -> __ -> typing -> 'a1 -> __ ->
    (Env.constructor_body, term branch, (((name binder_annot, term
    context_decl, __) coq_All2, typing) prod, typing) prod) coq_All2i -> 'a1)
    -> (Env.context -> projection -> term -> Instance.t ->
    Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.constructor_body -> Env.projection_body -> __ -> term list -> typing
    -> 'a1 -> __ -> 'a1) -> (Env.context -> term mfixpoint -> nat -> term def
    -> __ -> __ -> typing lift_typing coq_All_local_env -> (term def,
    (Universe.t, typing) sigT) coq_All -> (term def, typing) coq_All -> __ ->
    'a1) -> (Env.context -> term mfixpoint -> nat -> term def -> __ -> __ ->
    typing lift_typing coq_All_local_env -> (term def, (Universe.t, typing)
    sigT) coq_All -> (term def, typing) coq_All -> __ -> 'a1) -> (Env.context
    -> int -> kername -> Env.constant_body -> typing lift_typing
    coq_All_local_env -> __ -> __ -> Env.primitive_invariants -> 'a1) ->
    (Env.context -> float -> kername -> Env.constant_body -> typing
    lift_typing coq_All_local_env -> __ -> __ -> Env.primitive_invariants ->
    'a1) -> (Env.context -> term -> term -> term -> Universe.t -> typing ->
    'a1 -> typing -> 'a1 -> cumul_gen -> 'a1) -> Env.context -> term -> term
    -> typing -> 'a1 **)

let rec typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _UU0393_ _ _ = function
| Coq_type_Rel (n, decl, a) -> f _UU0393_ n decl a __
| Coq_type_Sort (s, a) -> f0 _UU0393_ s a __
| Coq_type_Cast (c, k, t0, s, t2, t3) ->
  f1 _UU0393_ c k t0 s t2
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 (Coq_tSort s) t2) t3
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ c t0 t3)
| Coq_type_Prod (n, t0, b, s1, s2, t2, t3) ->
  f2 _UU0393_ n t0 b s1 s2 t2
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 (Coq_tSort s1) t2) t3
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (snoc _UU0393_ (Env.vass n t0)) b (Coq_tSort s2) t3)
| Coq_type_Lambda (n, t0, b, s1, bty, t2, t3) ->
  f3 _UU0393_ n t0 b s1 bty t2
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 (Coq_tSort s1) t2) t3
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (snoc _UU0393_ (Env.vass n t0)) b bty t3)
| Coq_type_LetIn (n, b, b_ty, b', s1, b'_ty, t0, t2, t3) ->
  f4 _UU0393_ n b b_ty b' s1 b'_ty t0
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ b_ty (Coq_tSort s1) t0) t2
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ b b_ty t2) t3
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (snoc _UU0393_ (Env.vdef n b b_ty)) b' b'_ty t3)
| Coq_type_App (t0, l, t_ty, t', t2, t3) ->
  f5 _UU0393_ t0 l t_ty t' t2
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 t_ty t2) __ __ t3
| Coq_type_Const (cst, u, a, decl) -> f6 _UU0393_ cst u a decl __ __
| Coq_type_Ind (ind, u, a, mdecl, idecl) ->
  f7 _UU0393_ ind u a mdecl idecl __ __
| Coq_type_Construct (ind, i, u, a, mdecl, idecl, cdecl) ->
  f8 _UU0393_ ind i u a mdecl idecl cdecl __ __
| Coq_type_Case (ci, p, c, brs, indices, ps, mdecl, idecl, a, x, x0, x1, x2) ->
  let predctx = case_predicate_context ci.ci_ind mdecl idecl p in
  f9 _UU0393_ ci p c brs indices ps mdecl idecl __ __ a __ __ x x0
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (Env.app_context _UU0393_ predctx) p.preturn (Coq_tSort ps) x0)
    __ x1
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ c
      (mkApps (Coq_tInd (ci.ci_ind, p.puinst)) (app p.pparams indices)) x1)
    __ x2
| Coq_type_Proj (p, c, u, mdecl, idecl, cdecl, pdecl, args, t0) ->
  f10 _UU0393_ p c u mdecl idecl cdecl pdecl __ args t0
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ c (mkApps (Coq_tInd (p.proj_ind, u)) args) t0) __
| Coq_type_Fix (mfix, n, decl, a, a0, a1) ->
  f11 _UU0393_ mfix n decl __ __ a a0 a1 __
| Coq_type_CoFix (mfix, n, decl, a, a0, a1) ->
  f12 _UU0393_ mfix n decl __ __ a a0 a1 __
| Coq_type_Int (p, prim_ty, cdecl, a, p0) ->
  f13 _UU0393_ p prim_ty cdecl a __ __ p0
| Coq_type_Float (p, prim_ty, cdecl, a, p0) ->
  f14 _UU0393_ p prim_ty cdecl a __ __ p0
| Coq_type_Conv (t0, a, b, s, t2, t3, c) ->
  f15 _UU0393_ t0 a b s t2
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 a t2) t3
    (typing_rect h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ b (Coq_tSort s) t3) c

(** val typing_rec :
    checker_flags -> Env.global_env_ext -> (Env.context -> nat -> term
    context_decl -> typing lift_typing coq_All_local_env -> __ -> 'a1) ->
    (Env.context -> Universe.t -> typing lift_typing coq_All_local_env -> __
    -> 'a1) -> (Env.context -> term -> cast_kind -> term -> Universe.t ->
    typing -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term
    -> term -> Universe.t -> Universe.t -> typing -> 'a1 -> typing -> 'a1 ->
    'a1) -> (Env.context -> aname -> term -> term -> Universe.t -> term ->
    typing -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.context -> aname -> term
    -> term -> term -> Universe.t -> term -> typing -> 'a1 -> typing -> 'a1
    -> typing -> 'a1 -> 'a1) -> (Env.context -> term -> term list -> term ->
    term -> typing -> 'a1 -> __ -> __ -> typing_spine -> 'a1) -> (Env.context
    -> kername -> Instance.t -> typing lift_typing coq_All_local_env ->
    Env.constant_body -> __ -> __ -> 'a1) -> (Env.context -> inductive ->
    Instance.t -> typing lift_typing coq_All_local_env ->
    Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> __ -> 'a1)
    -> (Env.context -> inductive -> nat -> Instance.t -> typing lift_typing
    coq_All_local_env -> Env.mutual_inductive_body -> Env.one_inductive_body
    -> Env.constructor_body -> __ -> __ -> 'a1) -> (Env.context -> case_info
    -> term predicate -> term -> term branch list -> term list -> Universe.t
    -> Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> __ ->
    (name binder_annot, term context_decl, __) coq_All2 -> __ -> __ -> typing
    ctx_inst -> typing -> 'a1 -> __ -> typing -> 'a1 -> __ ->
    (Env.constructor_body, term branch, (((name binder_annot, term
    context_decl, __) coq_All2, typing) prod, typing) prod) coq_All2i -> 'a1)
    -> (Env.context -> projection -> term -> Instance.t ->
    Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.constructor_body -> Env.projection_body -> __ -> term list -> typing
    -> 'a1 -> __ -> 'a1) -> (Env.context -> term mfixpoint -> nat -> term def
    -> __ -> __ -> typing lift_typing coq_All_local_env -> (term def,
    (Universe.t, typing) sigT) coq_All -> (term def, typing) coq_All -> __ ->
    'a1) -> (Env.context -> term mfixpoint -> nat -> term def -> __ -> __ ->
    typing lift_typing coq_All_local_env -> (term def, (Universe.t, typing)
    sigT) coq_All -> (term def, typing) coq_All -> __ -> 'a1) -> (Env.context
    -> int -> kername -> Env.constant_body -> typing lift_typing
    coq_All_local_env -> __ -> __ -> Env.primitive_invariants -> 'a1) ->
    (Env.context -> float -> kername -> Env.constant_body -> typing
    lift_typing coq_All_local_env -> __ -> __ -> Env.primitive_invariants ->
    'a1) -> (Env.context -> term -> term -> term -> Universe.t -> typing ->
    'a1 -> typing -> 'a1 -> cumul_gen -> 'a1) -> Env.context -> term -> term
    -> typing -> 'a1 **)

let rec typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _UU0393_ _ _ = function
| Coq_type_Rel (n, decl, a) -> f _UU0393_ n decl a __
| Coq_type_Sort (s, a) -> f0 _UU0393_ s a __
| Coq_type_Cast (c, k, t0, s, t2, t3) ->
  f1 _UU0393_ c k t0 s t2
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 (Coq_tSort s) t2) t3
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ c t0 t3)
| Coq_type_Prod (n, t0, b, s1, s2, t2, t3) ->
  f2 _UU0393_ n t0 b s1 s2 t2
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 (Coq_tSort s1) t2) t3
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (snoc _UU0393_ (Env.vass n t0)) b (Coq_tSort s2) t3)
| Coq_type_Lambda (n, t0, b, s1, bty, t2, t3) ->
  f3 _UU0393_ n t0 b s1 bty t2
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 (Coq_tSort s1) t2) t3
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (snoc _UU0393_ (Env.vass n t0)) b bty t3)
| Coq_type_LetIn (n, b, b_ty, b', s1, b'_ty, t0, t2, t3) ->
  f4 _UU0393_ n b b_ty b' s1 b'_ty t0
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ b_ty (Coq_tSort s1) t0) t2
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ b b_ty t2) t3
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (snoc _UU0393_ (Env.vdef n b b_ty)) b' b'_ty t3)
| Coq_type_App (t0, l, t_ty, t', t2, t3) ->
  f5 _UU0393_ t0 l t_ty t' t2
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 t_ty t2) __ __ t3
| Coq_type_Const (cst, u, a, decl) -> f6 _UU0393_ cst u a decl __ __
| Coq_type_Ind (ind, u, a, mdecl, idecl) ->
  f7 _UU0393_ ind u a mdecl idecl __ __
| Coq_type_Construct (ind, i, u, a, mdecl, idecl, cdecl) ->
  f8 _UU0393_ ind i u a mdecl idecl cdecl __ __
| Coq_type_Case (ci, p, c, brs, indices, ps, mdecl, idecl, a, x, x0, x1, x2) ->
  let predctx = case_predicate_context ci.ci_ind mdecl idecl p in
  f9 _UU0393_ ci p c brs indices ps mdecl idecl __ __ a __ __ x x0
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 (Env.app_context _UU0393_ predctx) p.preturn (Coq_tSort ps) x0)
    __ x1
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ c
      (mkApps (Coq_tInd (ci.ci_ind, p.puinst)) (app p.pparams indices)) x1)
    __ x2
| Coq_type_Proj (p, c, u, mdecl, idecl, cdecl, pdecl, args, t0) ->
  f10 _UU0393_ p c u mdecl idecl cdecl pdecl __ args t0
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ c (mkApps (Coq_tInd (p.proj_ind, u)) args) t0) __
| Coq_type_Fix (mfix, n, decl, a, a0, a1) ->
  f11 _UU0393_ mfix n decl __ __ a a0 a1 __
| Coq_type_CoFix (mfix, n, decl, a, a0, a1) ->
  f12 _UU0393_ mfix n decl __ __ a a0 a1 __
| Coq_type_Int (p, prim_ty, cdecl, a, p0) ->
  f13 _UU0393_ p prim_ty cdecl a __ __ p0
| Coq_type_Float (p, prim_ty, cdecl, a, p0) ->
  f14 _UU0393_ p prim_ty cdecl a __ __ p0
| Coq_type_Conv (t0, a, b, s, t2, t3, c) ->
  f15 _UU0393_ t0 a b s t2
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ t0 a t2) t3
    (typing_rec h _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
      f14 f15 _UU0393_ b (Coq_tSort s) t3) c

(** val typing_spine_rect :
    checker_flags -> Env.global_env_ext -> (Env.context -> term -> 'a1) ->
    (Env.context -> term -> term list -> aname -> term -> term -> Universe.t
    -> term -> term -> typing -> cumul_gen -> typing -> typing_spine -> 'a1
    -> 'a1) -> Env.context -> term -> term list -> term -> typing_spine -> 'a1 **)

let rec typing_spine_rect h _UU03a3_ f f0 _UU0393_ _ _ _ = function
| Coq_type_spine_nil ty -> f _UU0393_ ty
| Coq_type_spine_cons (hd, tl, na, a, b, s, t0, b', t2, c, t3, t4) ->
  f0 _UU0393_ hd tl na a b s t0 b' t2 c t3 t4
    (typing_spine_rect h _UU03a3_ f f0 _UU0393_ (subst1 hd O b) tl b' t4)

(** val typing_spine_rec :
    checker_flags -> Env.global_env_ext -> (Env.context -> term -> 'a1) ->
    (Env.context -> term -> term list -> aname -> term -> term -> Universe.t
    -> term -> term -> typing -> cumul_gen -> typing -> typing_spine -> 'a1
    -> 'a1) -> Env.context -> term -> term list -> term -> typing_spine -> 'a1 **)

let rec typing_spine_rec h _UU03a3_ f f0 _UU0393_ _ _ _ = function
| Coq_type_spine_nil ty -> f _UU0393_ ty
| Coq_type_spine_cons (hd, tl, na, a, b, s, t0, b', t2, c, t3, t4) ->
  f0 _UU0393_ hd tl na a b s t0 b' t2 c t3 t4
    (typing_spine_rec h _UU03a3_ f f0 _UU0393_ (subst1 hd O b) tl b' t4)

type typing_sig = typing

(** val typing_sig_pack :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
    typing -> (Env.context * (term * term)) * typing **)

let typing_sig_pack _ _ _UU0393_ x x0 typing_var =
  (_UU0393_,(x,x0)),typing_var

(** val typing_Signature :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
    (typing, Env.context * (term * term), typing_sig) coq_Signature **)

let typing_Signature _ _ _UU0393_ x x0 typing_var =
  (_UU0393_,(x,x0)),typing_var

type typing_spine_sig = typing_spine

(** val typing_spine_sig_pack :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term list
    -> term -> typing_spine -> (Env.context * (term * (term
    list * term))) * typing_spine **)

let typing_spine_sig_pack _ _ _UU0393_ x x0 x1 typing_spine_var =
  (_UU0393_,(x,(x0,x1))),typing_spine_var

(** val typing_spine_Signature :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term list
    -> term -> (typing_spine, Env.context * (term * (term list * term)),
    typing_spine_sig) coq_Signature **)

let typing_spine_Signature _ _ _UU0393_ x x0 x1 typing_spine_var =
  (_UU0393_,(x,(x0,x1))),typing_spine_var

type 'p unlift_opt_pred = 'p

module Coq__3 = struct
 type infer_sorting = (Universe.t, typing) sigT
end
include Coq__3

module TemplateTyping =
 struct
  type typing = Coq__2.typing

  type infer_sorting = Coq__3.infer_sorting
 end

module TemplateDeclarationTyping =
 DeclarationTyping(TemplateTerm)(Env)(TemplateTermUtils)(TemplateEnvTyping)(TemplateConversion)(TemplateConversionPar)(TemplateTyping)(TemplateLookup)(TemplateGlobalMaps)

type isType = typing TemplateEnvTyping.infer_sort

type 'p coq_Forall_decls_typing =
  (cumul_gen, 'p TemplateEnvTyping.lift_typing)
  TemplateGlobalMaps.on_global_env

type type_local_decl = __

(** val refine_type :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
    term -> typing -> typing **)

let refine_type =
  TemplateDeclarationTyping.refine_type

type wf_local_rel =
  typing TemplateEnvTyping.lift_typing TemplateEnvTyping.coq_All_local_rel

(** val on_wf_global_env_impl_config :
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
    TemplateGlobalMaps.on_global_env **)

let on_wf_global_env_impl_config =
  TemplateDeclarationTyping.on_wf_global_env_impl_config

(** val on_wf_global_env_impl :
    checker_flags -> Env.global_env -> (cumul_gen, typing
    TemplateEnvTyping.lift_typing) TemplateGlobalMaps.on_global_env ->
    ((Env.global_env, universes_decl) prod -> Env.context -> term ->
    Env.typ_or_sort -> (cumul_gen, typing TemplateEnvTyping.lift_typing)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a1)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
    TemplateGlobalMaps.on_global_env -> 'a1 -> 'a2) -> (cumul_gen, 'a1)
    TemplateGlobalMaps.on_global_env -> (cumul_gen, 'a2)
    TemplateGlobalMaps.on_global_env **)

let on_wf_global_env_impl =
  TemplateDeclarationTyping.on_wf_global_env_impl

(** val typing_spine_size :
    checker_flags -> (Env.global_env_ext -> Env.context -> term -> term ->
    typing -> size) -> Env.global_env_ext -> Env.context -> term -> term list
    -> term -> typing_spine -> size **)

let rec typing_spine_size h fn _UU03a3_ _UU0393_ _ _ _ = function
| Coq_type_spine_nil _ -> O
| Coq_type_spine_cons (hd, tl, na, a, b, s0, _, b', typrod, _, ty, s') ->
  Nat.add
    (Nat.add (fn _UU03a3_ _UU0393_ hd a ty)
      (fn _UU03a3_ _UU0393_ (Coq_tProd (na, a, b)) (Coq_tSort s0) typrod))
    (typing_spine_size h fn _UU03a3_ _UU0393_ (subst1 hd O b) tl b' s')

(** val ctx_inst_size :
    (Env.global_env_ext -> Env.context -> term -> term -> 'a1 -> size) ->
    Env.global_env_ext -> Env.context -> term list -> Env.context -> 'a1
    ctx_inst -> size **)

let rec ctx_inst_size typing_size0 _UU03a3_ _UU0393_ _ _ = function
| Coq_ctx_inst_nil -> O
| Coq_ctx_inst_ass (_, t0, i, inst, _UU0394_, ty, ctxi) ->
  Nat.add (typing_size0 _UU03a3_ _UU0393_ i t0 ty)
    (ctx_inst_size typing_size0 _UU03a3_ _UU0393_ inst
      (Env.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_) ctxi)
| Coq_ctx_inst_def (_, b, _, inst, _UU0394_, ctxi) ->
  S
    (ctx_inst_size typing_size0 _UU03a3_ _UU0393_ inst
      (Env.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_) ctxi)

(** val typing_size :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
    typing -> size **)

let rec typing_size h _UU03a3_ _UU0393_ _ _ = function
| Coq_type_Rel (_, _, a) ->
  S
    (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
      typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a)
| Coq_type_Sort (_, a) ->
  S
    (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
      typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a)
| Coq_type_Cast (c, _, t0, s, t1, t2) ->
  let d2 = typing_size h _UU03a3_ _UU0393_ c t0 t2 in
  let d1 = typing_size h _UU03a3_ _UU0393_ t0 (Coq_tSort s) t1 in
  S (PeanoNat.Nat.max d1 d2)
| Coq_type_Prod (n, t0, b, s1, s2, t1, t2) ->
  let d2 =
    typing_size h _UU03a3_ (snoc _UU0393_ (Env.vass n t0)) b (Coq_tSort s2) t2
  in
  let d1 = typing_size h _UU03a3_ _UU0393_ t0 (Coq_tSort s1) t1 in
  S (PeanoNat.Nat.max d1 d2)
| Coq_type_Lambda (n, t0, b, s1, bty, t1, t2) ->
  let d2 = typing_size h _UU03a3_ (snoc _UU0393_ (Env.vass n t0)) b bty t2 in
  let d1 = typing_size h _UU03a3_ _UU0393_ t0 (Coq_tSort s1) t1 in
  S (PeanoNat.Nat.max d1 d2)
| Coq_type_LetIn (n, b, b_ty, b', s1, b'_ty, t0, t1, t2) ->
  let d3 =
    typing_size h _UU03a3_ (snoc _UU0393_ (Env.vdef n b b_ty)) b' b'_ty t2
  in
  let d2 = typing_size h _UU03a3_ _UU0393_ b b_ty t1 in
  let d1 = typing_size h _UU03a3_ _UU0393_ b_ty (Coq_tSort s1) t0 in
  S (PeanoNat.Nat.max d1 (PeanoNat.Nat.max d2 d3))
| Coq_type_App (t0, l, t_ty, t', t1, t2) ->
  let d0 = typing_size h _UU03a3_ _UU0393_ t0 t_ty t1 in
  S
  (PeanoNat.Nat.max d0
    (typing_spine_size h (fun x x0 x1 x2 x3 -> typing_size h x x0 x1 x2 x3)
      _UU03a3_ _UU0393_ t_ty l t' t2))
| Coq_type_Const (_, _, a, _) ->
  S (S
    (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
      typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a))
| Coq_type_Ind (_, _, a, _, _) ->
  S (S
    (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
      typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a))
| Coq_type_Construct (_, _, _, a, _, _, _) ->
  S (S
    (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
      typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a))
| Coq_type_Case (ci, p, c, brs, indices, ps, mdecl, idecl, _, x, x0, x1, x2) ->
  let predctx = case_predicate_context ci.ci_ind mdecl idecl p in
  let ptm = Env.it_mkLambda_or_LetIn predctx p.preturn in
  let d2 =
    typing_size h _UU03a3_ _UU0393_ c
      (mkApps (Coq_tInd (ci.ci_ind, p.puinst)) (app p.pparams indices)) x1
  in
  let d1 =
    typing_size h _UU03a3_ (Env.app_context _UU0393_ predctx) p.preturn
      (Coq_tSort ps) x0
  in
  S
  (PeanoNat.Nat.max d1
    (PeanoNat.Nat.max d2
      (PeanoNat.Nat.max
        (ctx_inst_size (fun x3 x4 x5 x6 x7 -> typing_size h x3 x4 x5 x6 x7)
          _UU03a3_ _UU0393_ (app p.pparams indices)
          (List.rev
            (subst_instance Env.subst_instance_context p.puinst
              (Env.app_context (Env.ind_params mdecl) (Env.ind_indices idecl))))
          x)
        (all2i_size (fun i x3 y p0 ->
          PeanoNat.Nat.max
            (typing_size h _UU03a3_
              (Env.app_context _UU0393_
                (fst (case_branch_type ci.ci_ind mdecl p ptm i x3 y)))
              y.bbody (snd (case_branch_type ci.ci_ind mdecl p ptm i x3 y))
              (snd (fst p0)))
            (typing_size h _UU03a3_
              (Env.app_context _UU0393_
                (fst (case_branch_type ci.ci_ind mdecl p ptm i x3 y)))
              (snd (case_branch_type ci.ci_ind mdecl p ptm i x3 y))
              (Coq_tSort ps) (snd p0))) O (Env.ind_ctors idecl) brs x2))))
| Coq_type_Proj (p, c, u, _, _, _, _, args, t0) ->
  let d0 =
    typing_size h _UU03a3_ _UU0393_ c
      (mkApps (Coq_tInd (p.proj_ind, u)) args) t0
  in
  S d0
| Coq_type_Fix (mfix, _, _, a, a0, a1) ->
  S
    (PeanoNat.Nat.max
      (PeanoNat.Nat.max
        (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
          typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a)
        (all_size (fun x p ->
          let t0 = x.dtype in
          let Coq_existT (s, d0) = p in
          typing_size h _UU03a3_ _UU0393_ t0 (Coq_tSort s) d0) mfix a0))
      (all_size (fun x p ->
        typing_size h _UU03a3_ (Env.app_context _UU0393_ (fix_context mfix))
          x.dbody (lift (length (fix_context mfix)) O x.dtype) p) mfix a1))
| Coq_type_CoFix (mfix, _, _, a, a0, a1) ->
  S
    (PeanoNat.Nat.max
      (PeanoNat.Nat.max
        (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
          typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a)
        (all_size (fun x p ->
          let t0 = x.dtype in
          let Coq_existT (s, d0) = p in
          typing_size h _UU03a3_ _UU0393_ t0 (Coq_tSort s) d0) mfix a0))
      (all_size (fun x p ->
        typing_size h _UU03a3_ (Env.app_context _UU0393_ (fix_context mfix))
          x.dbody (lift (length (fix_context mfix)) O x.dtype) p) mfix a1))
| Coq_type_Int (_, _, _, a, _) ->
  S
    (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
      typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a)
| Coq_type_Float (_, _, _, a, _) ->
  S
    (coq_All_local_env_size (fun x x0 x1 x2 x3 ->
      typing_size h x x0 x1 x2 x3) _UU03a3_ _UU0393_ a)
| Coq_type_Conv (t0, a, b, s, t1, t2, _) ->
  let d2 = typing_size h _UU03a3_ _UU0393_ b (Coq_tSort s) t2 in
  let d1 = typing_size h _UU03a3_ _UU0393_ t0 a t1 in
  S (PeanoNat.Nat.max d1 d2)

(** val globdecls_size : Env.global_declarations -> size **)

let rec globdecls_size = function
| Coq_nil -> S O
| Coq_cons (_, _UU03a3_0) -> S (globdecls_size _UU03a3_0)

(** val globenv_size : Env.global_env -> size **)

let globenv_size _UU03a3_ =
  globdecls_size (Env.declarations _UU03a3_)

type wf = (cumul_gen, typing lift_typing) on_global_env

type wf_ext = (cumul_gen, typing lift_typing) on_global_env_ext

(** val typing_wf_local :
    checker_flags -> Env.global_env_ext -> Env.context -> term -> term ->
    typing -> typing lift_typing coq_All_local_env **)

let rec typing_wf_local h _UU03a3_ _UU0393_ _ _ = function
| Coq_type_Rel (_, _, a) -> a
| Coq_type_Sort (_, a) -> a
| Coq_type_Cast (c, _, t0, _, _, t1) ->
  typing_wf_local h _UU03a3_ _UU0393_ c t0 t1
| Coq_type_Prod (_, t0, _, s1, _, t1, _) ->
  typing_wf_local h _UU03a3_ _UU0393_ t0 (Coq_tSort s1) t1
| Coq_type_Lambda (_, t0, _, s1, _, t1, _) ->
  typing_wf_local h _UU03a3_ _UU0393_ t0 (Coq_tSort s1) t1
| Coq_type_LetIn (_, b, b_ty, _, _, _, _, t0, _) ->
  typing_wf_local h _UU03a3_ _UU0393_ b b_ty t0
| Coq_type_App (t0, _, t_ty, _, t1, _) ->
  typing_wf_local h _UU03a3_ _UU0393_ t0 t_ty t1
| Coq_type_Const (_, _, a, _) -> a
| Coq_type_Ind (_, _, a, _, _) -> a
| Coq_type_Construct (_, _, _, a, _, _, _) -> a
| Coq_type_Case (ci, p, c, _, indices, _, _, _, _, _, _, x0, _) ->
  typing_wf_local h _UU03a3_ _UU0393_ c
    (mkApps (Coq_tInd (ci.ci_ind, p.puinst)) (app p.pparams indices)) x0
| Coq_type_Proj (p, c, u, _, _, _, _, args, t0) ->
  typing_wf_local h _UU03a3_ _UU0393_ c
    (mkApps (Coq_tInd (p.proj_ind, u)) args) t0
| Coq_type_Fix (_, _, _, a, _, _) -> a
| Coq_type_CoFix (_, _, _, a, _, _) -> a
| Coq_type_Int (_, _, _, a, _) -> a
| Coq_type_Float (_, _, _, a, _) -> a
| Coq_type_Conv (_, _, b, s, _, t0, _) ->
  typing_wf_local h _UU03a3_ _UU0393_ b (Coq_tSort s) t0

(** val type_Prop : checker_flags -> Env.global_env_ext -> typing **)

let type_Prop _ _ =
  Coq_type_Sort (Universe.Coq_lProp, Coq_localenv_nil)

(** val type_Prop_wf :
    checker_flags -> Env.global_env_ext -> Env.context -> typing lift_typing
    coq_All_local_env -> typing **)

let type_Prop_wf _ _ _ x =
  Coq_type_Sort (Universe.Coq_lProp, x)

type ('p, 'x) env_prop =
  Env.global_env_ext -> wf -> Env.context -> typing lift_typing
  coq_All_local_env -> term -> term -> typing -> ((cumul_gen, 'p lift_typing)
  on_global_env, ('x, 'p) prod) prod

(** val env_prop_typing :
    checker_flags -> ('a1, 'a2) env_prop -> Env.global_env_ext -> wf ->
    Env.context -> typing lift_typing coq_All_local_env -> term -> term ->
    typing -> 'a1 **)

let env_prop_typing _ x _UU03a3_ wf_UU03a3_ _UU0393_ wf_UU0393_ t0 t1 x0 =
  let x1 = fun _UU03a3_0 wf_UU03a3_0 _UU0393_0 wf_UU0393_0 t2 t3 ty ->
    let Coq_pair (_, x1) =
      x _UU03a3_0 wf_UU03a3_0 _UU0393_0 wf_UU0393_0 t2 t3 ty
    in
    x1
  in
  let Coq_pair (_, x2) = x1 _UU03a3_ wf_UU03a3_ _UU0393_ wf_UU0393_ t0 t1 x0
  in
  x2

(** val env_prop_wf_local :
    checker_flags -> ('a1, 'a2) env_prop -> Env.global_env_ext -> wf ->
    Env.context -> typing lift_typing coq_All_local_env -> 'a2 **)

let env_prop_wf_local h x _UU03a3_ wf_UU03a3_ _UU0393_ wf_UU0393_ =
  let x0 =
    let Coq_pair (_, x0) =
      x _UU03a3_ wf_UU03a3_ _UU0393_ wf_UU0393_ (Coq_tSort
        Universe.Coq_lProp) (Coq_tSort Universe.type1)
        (type_Prop_wf h _UU03a3_ _UU0393_ wf_UU0393_)
    in
    x0
  in
  let Coq_pair (x1, _) = x0 in x1

(** val env_prop_sigma :
    checker_flags -> ('a1, 'a2) env_prop -> Env.global_env -> wf ->
    (cumul_gen, 'a1 lift_typing) on_global_env **)

let env_prop_sigma h x _UU03a3_ wf_UU03a3_ =
  let _UU0393_ = Coq_nil in
  let wf_UU0393_ = Coq_localenv_nil in
  let t0 = Coq_tSort Universe.Coq_lProp in
  let t1 = Coq_tSort Universe.type1 in
  let ty = type_Prop h (Env.empty_ext _UU03a3_) in
  let Coq_pair (x0, _) =
    x (Env.empty_ext _UU03a3_) wf_UU03a3_ _UU0393_ wf_UU0393_ t0 t1 ty
  in
  x0

(** val wf_local_app_l :
    checker_flags -> Env.global_env_ext -> Env.context -> Env.context ->
    typing lift_typing coq_All_local_env -> typing lift_typing
    coq_All_local_env **)

let rec wf_local_app_l h _UU03a3_ _UU0393_ _UU0393_' x =
  match _UU0393_' with
  | Coq_nil -> x
  | Coq_cons (_, l) ->
    (match x with
     | Coq_localenv_nil -> assert false (* absurd case *)
     | Coq_localenv_cons_abs (_, _, _, x0, _) ->
       wf_local_app_l h _UU03a3_ _UU0393_ l x0
     | Coq_localenv_cons_def (_, _, _, _, x0, _, _) ->
       wf_local_app_l h _UU03a3_ _UU0393_ l x0)

(** val wf_local_inv :
    checker_flags -> Env.global_env_ext -> Env.context -> typing lift_typing
    coq_All_local_env -> term context_decl -> term context_decl list ->
    (typing lift_typing coq_All_local_env, __) sigT **)

let wf_local_inv _ _ _ w _ _ =
  match w with
  | Coq_localenv_nil -> assert false (* absurd case *)
  | Coq_localenv_cons_abs (_, _, _, a, l) ->
    Coq_existT (a,
      (let Coq_existT (x, t0) = Obj.magic l in Obj.magic (Coq_existT (x, t0))))
  | Coq_localenv_cons_def (_, _, _, _, a, l, l0) ->
    Coq_existT (a,
      (let Coq_existT (x, t0) = Obj.magic l in
       Obj.magic (Coq_existT (x, (Coq_existT (l0, t0))))))

type 'p coq_Forall_typing_spine =
| Forall_type_spine_nil of term
| Forall_type_spine_cons of term * term list * aname * term * term
   * Universe.t * term * term * typing_spine * typing * cumul_gen * typing
   * 'p * 'p * 'p coq_Forall_typing_spine

(** val coq_Forall_typing_spine_rect :
    checker_flags -> Env.global_env_ext -> Env.context -> (term -> 'a2) ->
    (term -> term list -> aname -> term -> term -> Universe.t -> term -> term
    -> typing_spine -> typing -> cumul_gen -> typing -> 'a1 -> 'a1 -> 'a1
    coq_Forall_typing_spine -> 'a2 -> 'a2) -> term -> term list -> term ->
    typing_spine -> 'a1 coq_Forall_typing_spine -> 'a2 **)

let rec coq_Forall_typing_spine_rect h _UU03a3_ _UU0393_ f f0 _ _ _ _ = function
| Forall_type_spine_nil t0 -> f t0
| Forall_type_spine_cons (hd, tl, na, a, b, s, t0, b', tls, typrod, cumul,
                          ty, y, y0, f2) ->
  f0 hd tl na a b s t0 b' tls typrod cumul ty y y0 f2
    (coq_Forall_typing_spine_rect h _UU03a3_ _UU0393_ f f0 (subst1 hd O b) tl
      b' tls f2)

(** val coq_Forall_typing_spine_rec :
    checker_flags -> Env.global_env_ext -> Env.context -> (term -> 'a2) ->
    (term -> term list -> aname -> term -> term -> Universe.t -> term -> term
    -> typing_spine -> typing -> cumul_gen -> typing -> 'a1 -> 'a1 -> 'a1
    coq_Forall_typing_spine -> 'a2 -> 'a2) -> term -> term list -> term ->
    typing_spine -> 'a1 coq_Forall_typing_spine -> 'a2 **)

let rec coq_Forall_typing_spine_rec h _UU03a3_ _UU0393_ f f0 _ _ _ _ = function
| Forall_type_spine_nil t0 -> f t0
| Forall_type_spine_cons (hd, tl, na, a, b, s, t0, b', tls, typrod, cumul,
                          ty, y, y0, f2) ->
  f0 hd tl na a b s t0 b' tls typrod cumul ty y y0 f2
    (coq_Forall_typing_spine_rec h _UU03a3_ _UU0393_ f f0 (subst1 hd O b) tl
      b' tls f2)

(** val typing_ind_env :
    checker_flags -> (Env.global_env_ext -> wf -> Env.context -> typing
    lift_typing coq_All_local_env -> (typing, 'a1) coq_All_local_env_over ->
    'a2) -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> nat -> term context_decl -> __ -> 'a2 -> 'a1) ->
    (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> Universe.t -> 'a2 -> __ -> 'a1) ->
    (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> term -> cast_kind -> term -> Universe.t -> typing ->
    'a1 -> typing -> 'a1 -> 'a1) -> (Env.global_env_ext -> wf -> Env.context
    -> typing lift_typing coq_All_local_env -> aname -> term -> term ->
    Universe.t -> Universe.t -> 'a2 -> typing -> 'a1 -> typing -> 'a1 -> 'a1)
    -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> aname -> term -> term -> Universe.t -> term -> 'a2
    -> typing -> 'a1 -> typing -> 'a1 -> 'a1) -> (Env.global_env_ext -> wf ->
    Env.context -> typing lift_typing coq_All_local_env -> aname -> term ->
    term -> term -> Universe.t -> term -> 'a2 -> typing -> 'a1 -> typing ->
    'a1 -> typing -> 'a1 -> 'a1) -> (Env.global_env_ext -> wf -> Env.context
    -> typing lift_typing coq_All_local_env -> term -> term list -> term ->
    term -> typing -> 'a1 -> __ -> __ -> typing_spine -> 'a1
    coq_Forall_typing_spine -> 'a1) -> (Env.global_env_ext -> wf ->
    Env.context -> typing lift_typing coq_All_local_env -> kername ->
    Instance.t -> Env.constant_body -> (cumul_gen, 'a1 lift_typing)
    on_global_env -> 'a2 -> __ -> __ -> 'a1) -> (Env.global_env_ext -> wf ->
    Env.context -> typing lift_typing coq_All_local_env -> inductive ->
    Instance.t -> Env.mutual_inductive_body -> Env.one_inductive_body -> __
    -> (cumul_gen, 'a1 lift_typing) on_global_env -> 'a2 -> __ -> 'a1) ->
    (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> inductive -> nat -> Instance.t ->
    Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.constructor_body -> __ -> (cumul_gen, 'a1 lift_typing) on_global_env
    -> 'a2 -> __ -> 'a1) -> (Env.global_env_ext -> wf -> Env.context ->
    typing lift_typing coq_All_local_env -> case_info -> term predicate ->
    term -> term branch list -> term list -> Universe.t ->
    Env.mutual_inductive_body -> Env.one_inductive_body -> __ -> (cumul_gen,
    'a1 lift_typing) on_global_env -> 'a2 -> __ -> (name binder_annot, term
    context_decl, __) coq_All2 -> __ -> __ -> (typing, 'a1) prod ctx_inst ->
    typing -> 'a1 -> 'a2 -> __ -> typing -> 'a1 -> __ ->
    (Env.constructor_body, term branch, (((name binder_annot, term
    context_decl, __) coq_All2, (typing, 'a1) prod) prod, (typing, 'a1) prod)
    prod) coq_All2i -> 'a1) -> (Env.global_env_ext -> wf -> Env.context ->
    typing lift_typing coq_All_local_env -> projection -> term -> Instance.t
    -> Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.constructor_body -> Env.projection_body -> __ -> term list ->
    (cumul_gen, 'a1 lift_typing) on_global_env -> 'a2 -> typing -> 'a1 -> __
    -> 'a1) -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> term def list -> nat -> term def -> __ -> __ -> 'a2
    -> (term def, (typing, 'a1) lift_typing2 on_def_type) coq_All -> (term
    def, (typing, 'a1) lift_typing2 on_def_body) coq_All -> __ -> 'a1) ->
    (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> term def list -> nat -> term def -> __ -> __ -> 'a2
    -> (term def, (typing, 'a1) lift_typing2 on_def_type) coq_All -> (term
    def, (typing, 'a1) lift_typing2 on_def_body) coq_All -> __ -> 'a1) ->
    (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> int -> kername -> Env.constant_body -> 'a2 -> __ ->
    __ -> Env.primitive_invariants -> 'a1) -> (Env.global_env_ext -> wf ->
    Env.context -> typing lift_typing coq_All_local_env -> float -> kername
    -> Env.constant_body -> 'a2 -> __ -> __ -> Env.primitive_invariants ->
    'a1) -> (Env.global_env_ext -> wf -> Env.context -> typing lift_typing
    coq_All_local_env -> term -> term -> term -> Universe.t -> 'a2 -> typing
    -> 'a1 -> typing -> 'a1 -> cumul_gen -> 'a1) -> ('a1, 'a2) env_prop **)

let typing_ind_env cf x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 _UU03a3_ wf_UU03a3_ _UU0393_ _ t0 t1 ty =
  let p0 = fun x17 x18 ->
    let rec fix_F x19 =
      x17 x19 (fun y _ -> fix_F y)
    in fix_F x18
  in
  let h0 = fun x17 iH ->
    let Coq_existT (x18, s) = x17 in
    let Coq_existT (x19, s0) = s in
    let Coq_existT (x20, s1) = s0 in
    let Coq_existT (x21, s2) = s1 in
    let Coq_existT (x22, t2) = s2 in
    Coq_pair
    ((let Coq_pair (g, _) = x18 in
      let { Env.universes = universes0; Env.declarations = _;
        Env.retroknowledge = retroknowledge0 } = g
      in
      let Coq_pair (_, o) = x19 in
      Coq_pair (__,
      (match o with
       | Coq_globenv_nil -> Coq_globenv_nil
       | Coq_globenv_decl (_UU03a3_0, kn, d, o0, o1) ->
         let wf_UU03a3_0 = Coq_pair (__, o0) in
         let _UU03a3_' = { Env.universes = universes0; Env.declarations =
           _UU03a3_0; Env.retroknowledge = retroknowledge0 }
         in
         let udecl0 = TemplateLookup.universes_decl_of_decl d in
         Coq_globenv_decl (_UU03a3_0, kn, d,
         (let iH' =
            Obj.magic iH (Coq_existT ((Coq_pair (_UU03a3_', udecl0)),
              (Coq_existT (wf_UU03a3_0, (Coq_existT (Coq_nil, (Coq_existT
              ((Coq_tSort Universe.Coq_lProp), (Coq_existT ((Coq_tSort
              Universe.type1),
              (type_Prop cf (Coq_pair (_UU03a3_', udecl0)))))))))))))
          in
          let iH'0 = iH' __ in
          let x23 = let Coq_pair (x23, _) = iH'0 in x23 in
          let Coq_pair (_, x24) = x23 in x24),
         (match d with
          | Env.ConstantDecl c ->
            let { Env.cst_type = cst_type0; Env.cst_body = cst_body0;
              Env.cst_universes = cst_universes0; Env.cst_relevance =
              cst_relevance0 } = c
            in
            let udecl1 =
              TemplateLookup.universes_decl_of_decl (Env.ConstantDecl
                { Env.cst_type = cst_type0; Env.cst_body = cst_body0;
                Env.cst_universes = cst_universes0; Env.cst_relevance =
                cst_relevance0 })
            in
            (match cst_body0 with
             | Some t3 ->
               lift_typing_impl (Coq_pair ({ Env.universes = universes0;
                 Env.declarations = _UU03a3_0; Env.retroknowledge =
                 retroknowledge0 }, udecl1)) (Coq_pair ({ Env.universes =
                 universes0; Env.declarations = _UU03a3_0;
                 Env.retroknowledge = retroknowledge0 }, cst_universes0))
                 Coq_nil Coq_nil t3 t3 (Typ
                 (Env.cst_type { Env.cst_type = cst_type0; Env.cst_body =
                   (Some t3); Env.cst_universes = cst_universes0;
                   Env.cst_relevance = cst_relevance0 })) o1 (fun t4 hs ->
                 let iH0 =
                   iH (Coq_existT ((Coq_pair (_UU03a3_', udecl1)),
                     (Coq_existT (wf_UU03a3_0, (Coq_existT (Coq_nil,
                     (Coq_existT (t3, (Coq_existT (t4, hs))))))))))
                 in
                 let iH1 = iH0 __ in
                 let x23 = let Coq_pair (_, x23) = iH1 in x23 in
                 let Coq_pair (_, x24) = x23 in x24)
             | None ->
               lift_typing_impl (Coq_pair ({ Env.universes = universes0;
                 Env.declarations = _UU03a3_0; Env.retroknowledge =
                 retroknowledge0 }, udecl1)) (Coq_pair ({ Env.universes =
                 universes0; Env.declarations = _UU03a3_0;
                 Env.retroknowledge = retroknowledge0 }, cst_universes0))
                 Coq_nil Coq_nil
                 (Env.cst_type { Env.cst_type = cst_type0; Env.cst_body =
                   None; Env.cst_universes = cst_universes0;
                   Env.cst_relevance = cst_relevance0 })
                 (Env.cst_type { Env.cst_type = cst_type0; Env.cst_body =
                   None; Env.cst_universes = cst_universes0;
                   Env.cst_relevance = cst_relevance0 }) Sort o1
                 (fun t3 hs ->
                 let iH0 =
                   iH (Coq_existT ((Coq_pair (_UU03a3_', udecl1)),
                     (Coq_existT (wf_UU03a3_0, (Coq_existT (Coq_nil,
                     (Coq_existT
                     ((Env.cst_type { Env.cst_type = cst_type0;
                        Env.cst_body = None; Env.cst_universes =
                        cst_universes0; Env.cst_relevance = cst_relevance0 }),
                     (Coq_existT (t3, hs))))))))))
                 in
                 let iH1 = iH0 __ in
                 let x23 = let Coq_pair (_, x23) = iH1 in x23 in
                 let Coq_pair (_, x24) = x23 in x24))
          | Env.InductiveDecl m ->
            let udecl1 =
              TemplateLookup.universes_decl_of_decl (Env.InductiveDecl m)
            in
            let { onInductives = onInductives0; onParams = onParams0;
              onVariance = onVariance0 } = Obj.magic o1
            in
            Obj.magic { onInductives =
              (let iH' = fun p ->
                 iH (Coq_existT ((Coq_pair (_UU03a3_', udecl1)), (Coq_existT
                   (wf_UU03a3_0, p)))) __
               in
               coq_Alli_impl (Env.ind_bodies m) O onInductives0
                 (fun n x23 xg -> { onArity =
                 (let xg0 =
                    onArity cf (Coq_pair ({ Env.universes = universes0;
                      Env.declarations = _UU03a3_0; Env.retroknowledge =
                      retroknowledge0 }, udecl1)) kn m n x23 xg
                  in
                  lift_typing_impl (Coq_pair ({ Env.universes = universes0;
                    Env.declarations = _UU03a3_0; Env.retroknowledge =
                    retroknowledge0 }, udecl1)) (Coq_pair ({ Env.universes =
                    universes0; Env.declarations = _UU03a3_0;
                    Env.retroknowledge = retroknowledge0 },
                    (TemplateLookup.universes_decl_of_decl (Env.InductiveDecl
                      m)))) Coq_nil Coq_nil (Env.ind_type x23)
                    (Env.ind_type x23) Sort xg0 (fun t3 hs ->
                    let x24 =
                      let Coq_pair (_, x24) =
                        iH' (Coq_existT (Coq_nil, (Coq_existT
                          ((Env.ind_type x23), (Coq_existT (t3, hs))))))
                      in
                      x24
                    in
                    let Coq_pair (_, x25) = x24 in x25)); ind_cunivs =
                 (ind_cunivs cf (Coq_pair ({ Env.universes = universes0;
                   Env.declarations = _UU03a3_0; Env.retroknowledge =
                   retroknowledge0 }, udecl1)) kn m n x23 xg);
                 onConstructors =
                 (let xg' =
                    onConstructors cf (Coq_pair ({ Env.universes =
                      universes0; Env.declarations = _UU03a3_0;
                      Env.retroknowledge = retroknowledge0 }, udecl1)) kn m n
                      x23 xg
                  in
                  coq_All2_impl (Env.ind_ctors x23)
                    (ind_cunivs cf (Coq_pair ({ Env.universes = universes0;
                      Env.declarations = _UU03a3_0; Env.retroknowledge =
                      retroknowledge0 }, udecl1)) kn m n x23 xg) xg'
                    (fun x24 y x25 ->
                    let { on_ctype = on_ctype0; on_cargs = on_cargs0;
                      on_cindices = on_cindices0; on_ctype_positive =
                      on_ctype_positive0; on_ctype_variance =
                      on_ctype_variance0 } = x25
                    in
                    { on_ctype =
                    (lift_typing_impl (Coq_pair ({ Env.universes =
                      universes0; Env.declarations = _UU03a3_0;
                      Env.retroknowledge = retroknowledge0 }, udecl1))
                      (Coq_pair ({ Env.universes = universes0;
                      Env.declarations = _UU03a3_0; Env.retroknowledge =
                      retroknowledge0 },
                      (TemplateLookup.universes_decl_of_decl
                        (Env.InductiveDecl m))))
                      (Env.arities_context (Env.ind_bodies m))
                      (Env.arities_context (Env.ind_bodies m))
                      (Env.cstr_type x24) (Env.cstr_type x24) Sort on_ctype0
                      (fun t3 hs ->
                      let x26 =
                        let Coq_pair (_, x26) =
                          iH' (Coq_existT
                            ((Env.arities_context (Env.ind_bodies m)),
                            (Coq_existT ((Env.cstr_type x24), (Coq_existT
                            (t3, hs))))))
                        in
                        x26
                      in
                      let Coq_pair (_, x27) = x26 in x27)); on_cargs =
                    (sorts_local_ctx_impl (Coq_pair ({ Env.universes =
                      universes0; Env.declarations = _UU03a3_0;
                      Env.retroknowledge = retroknowledge0 }, udecl1))
                      (Env.app_context
                        (Env.arities_context (Env.ind_bodies m))
                        (Env.ind_params m)) (Env.cstr_args x24) y on_cargs0
                      (fun _UU0393_' t' t'0 hT' ->
                      lift_typing_impl (Coq_pair ({ Env.universes =
                        universes0; Env.declarations = _UU03a3_0;
                        Env.retroknowledge = retroknowledge0 }, udecl1))
                        (Coq_pair ({ Env.universes = universes0;
                        Env.declarations = _UU03a3_0; Env.retroknowledge =
                        retroknowledge0 }, udecl1)) _UU0393_' _UU0393_' t' t'
                        t'0 hT' (fun t3 hs ->
                        let x26 =
                          let Coq_pair (_, x26) =
                            iH' (Coq_existT (_UU0393_', (Coq_existT (t',
                              (Coq_existT (t3, hs))))))
                          in
                          x26
                        in
                        let Coq_pair (_, x27) = x26 in x27))); on_cindices =
                    (let l = Env.cstr_indices x24 in
                     let l0 =
                       List.rev
                         (Env.lift_context (length (Env.cstr_args x24)) O
                           (Env.ind_indices x23))
                     in
                     TemplateEnvTyping.ctx_inst_rect (Coq_pair
                       ({ Env.universes = universes0; Env.declarations =
                       _UU03a3_0; Env.retroknowledge = retroknowledge0 },
                       udecl1))
                       (Env.app_context
                         (Env.app_context
                           (Env.arities_context (Env.ind_bodies m))
                           (Env.ind_params m)) (Env.cstr_args x24))
                       TemplateEnvTyping.Coq_ctx_inst_nil
                       (fun na t3 i inst _UU0394_ t4 _ iHoncind ->
                       TemplateEnvTyping.Coq_ctx_inst_ass (na, t3, i, inst,
                       _UU0394_,
                       (let x26 =
                          let Coq_pair (_, x26) =
                            iH' (Coq_existT
                              ((Env.app_context
                                 (Env.app_context
                                   (Env.arities_context (Env.ind_bodies m))
                                   (Env.ind_params m)) (Env.cstr_args x24)),
                              (Coq_existT (i, (Coq_existT (t3, t4))))))
                          in
                          x26
                        in
                        let Coq_pair (_, x27) = x26 in x27), iHoncind))
                       (fun na b t3 inst _UU0394_ _ iHoncind ->
                       TemplateEnvTyping.Coq_ctx_inst_def (na, b, t3, inst,
                       _UU0394_, iHoncind)) l l0 on_cindices0);
                    on_ctype_positive = on_ctype_positive0;
                    on_ctype_variance = on_ctype_variance0 }));
                 onProjections =
                 (onProjections cf (Coq_pair ({ Env.universes = universes0;
                   Env.declarations = _UU03a3_0; Env.retroknowledge =
                   retroknowledge0 }, udecl1)) kn m n x23 xg); ind_sorts =
                 (let { onArity = _; ind_cunivs = _; onConstructors = _;
                    onProjections = _; ind_sorts = ind_sorts0; onIndices =
                    _ } = xg
                  in
                  let b = Universe.is_prop (Env.ind_sort x23) in
                  (match b with
                   | Coq_true -> Obj.magic __ ind_sorts0
                   | Coq_false ->
                     let b0 = Universe.is_sprop (Env.ind_sort x23) in
                     (match b0 with
                      | Coq_true -> Obj.magic __ ind_sorts0
                      | Coq_false ->
                        Obj.magic (Coq_pair (__,
                          (let b1 = cf.indices_matter in
                           match b1 with
                           | Coq_true ->
                             type_local_ctx_impl (Coq_pair ({ Env.universes =
                               universes0; Env.declarations = _UU03a3_0;
                               Env.retroknowledge = retroknowledge0 },
                               (Env.ind_universes m))) (Env.ind_params m)
                               (Env.ind_indices x23) (Env.ind_sort x23)
                               (let Coq_pair (_, x24) = Obj.magic ind_sorts0
                                in
                                x24) (fun _UU0393_0 t3 t4 hT ->
                               lift_typing_impl (Coq_pair ({ Env.universes =
                                 universes0; Env.declarations = _UU03a3_0;
                                 Env.retroknowledge = retroknowledge0 },
                                 (Env.ind_universes m))) (Coq_pair
                                 ({ Env.universes = universes0;
                                 Env.declarations = _UU03a3_0;
                                 Env.retroknowledge = retroknowledge0 },
                                 (Env.ind_universes m))) _UU0393_0 _UU0393_0
                                 t3 t3 t4 hT (fun t5 hs ->
                                 let x24 =
                                   let Coq_pair (_, x24) =
                                     iH' (Coq_existT (_UU0393_0, (Coq_existT
                                       (t3, (Coq_existT (t5, hs))))))
                                   in
                                   x24
                                 in
                                 let Coq_pair (_, x25) = x24 in x25))
                           | Coq_false -> Obj.magic __ ind_sorts0))))));
                 onIndices =
                 (onIndices cf (Coq_pair ({ Env.universes = universes0;
                   Env.declarations = _UU03a3_0; Env.retroknowledge =
                   retroknowledge0 }, udecl1)) kn m n x23 xg) })); onParams =
              (coq_All_local_env_impl (Env.ind_params m) onParams0
                (fun _UU0393_0 t3 t4 hT ->
                lift_typing_impl (Coq_pair ({ Env.universes = universes0;
                  Env.declarations = _UU03a3_0; Env.retroknowledge =
                  retroknowledge0 }, udecl1)) (Coq_pair ({ Env.universes =
                  universes0; Env.declarations = _UU03a3_0;
                  Env.retroknowledge = retroknowledge0 },
                  (TemplateLookup.universes_decl_of_decl (Env.InductiveDecl
                    m)))) _UU0393_0 _UU0393_0 t3 t3 t4 hT (fun t5 hs ->
                  let x23 = fun _ ->
                    let Coq_pair (_, x23) =
                      iH (Coq_existT ((Coq_pair (_UU03a3_', udecl1)),
                        (Coq_existT (wf_UU03a3_0, (Coq_existT (_UU0393_0,
                        (Coq_existT (t3, (Coq_existT (t5, hs)))))))))) __
                    in
                    x23
                  in
                  let Coq_pair (_, x24) = x23 __ in x24))); onVariance =
              onVariance0 }))))),
    (let x23 = fun _UU0393_0 t3 t4 hty ->
       let iH0 =
         iH (Coq_existT (x18, (Coq_existT (x19, (Coq_existT (_UU0393_0,
           (Coq_existT (t3, (Coq_existT (t4, hty))))))))))
       in
       let iH1 = iH0 __ in
       let Coq_pair (a, b) = iH1 in
       let Coq_pair (_, b0) = b in Coq_pair (a, b0)
     in
     let x24 = fun _UU0393_' t3 t4 hty ->
       Obj.magic x x18 x19 _UU0393_'
         (typing_wf_local cf x18 _UU0393_' t3 t4 hty)
         (let foo = typing_wf_local cf x18 _UU0393_' t3 t4 hty in
          let rec f _ = function
          | Coq_localenv_nil -> Coq_localenv_over_nil
          | Coq_localenv_cons_abs (_UU0393_0, na, t5, a0, t6) ->
            let Coq_existT (x24, t7) = Obj.magic t6 in
            Coq_localenv_over_cons_abs (_UU0393_0, na, t5, a0,
            (f _UU0393_0 a0), (Obj.magic (Coq_existT (x24, t7))),
            (let Coq_pair (_, x25) = x23 _UU0393_0 t5 (Coq_tSort x24) t7 in
             x25))
          | Coq_localenv_cons_def (_UU0393_0, na, b, t5, a0, t6, t7) ->
            let Coq_existT (x24, t8) = Obj.magic t6 in
            Coq_localenv_over_cons_def (_UU0393_0, na, b, t5, a0, t7,
            (f _UU0393_0 a0),
            (let Coq_pair (_, x25) = x23 _UU0393_0 b t5 t7 in x25),
            (Obj.magic (Coq_existT (x24, t8))),
            (let Coq_pair (_, x25) = x23 _UU0393_0 t5 (Coq_tSort x24) t8 in
             x25))
          in f _UU0393_' foo)
     in
     let p_UU0393_ = x24 x20 x21 x22 t2 in
     Coq_pair (p_UU0393_,
     (let wf_UU0393_ = typing_wf_local cf x18 x20 x21 x22 t2 in
      match t2 with
      | Coq_type_Rel (n, decl, a) -> x0 x18 x19 x20 a n decl __ p_UU0393_
      | Coq_type_Sort (s3, a) -> x1 x18 x19 x20 a s3 p_UU0393_ __
      | Coq_type_Cast (c, k, t3, s3, t4, t5) ->
        x2 x18 x19 x20 wf_UU0393_ c k t3 s3 t4
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 t3 (Coq_tSort s3) t4) t5
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 c t3 t5)
      | Coq_type_Prod (n, t3, b, s3, s4, t4, t5) ->
        x3 x18 x19 x20 (typing_wf_local cf x18 x20 t3 (Coq_tSort s3) t4) n t3
          b s3 s4 p_UU0393_ t4
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 t3 (Coq_tSort s3) t4) t5
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 (snoc x20 (Env.vass n t3)) b (Coq_tSort s4) t5)
      | Coq_type_Lambda (n, t3, b, s3, bty, t4, t5) ->
        x4 x18 x19 x20 (typing_wf_local cf x18 x20 t3 (Coq_tSort s3) t4) n t3
          b s3 bty p_UU0393_ t4
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 t3 (Coq_tSort s3) t4) t5
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 (snoc x20 (Env.vass n t3)) b bty t5)
      | Coq_type_LetIn (n, b, b_ty, b', s3, b'_ty, t3, t4, t5) ->
        x5 x18 x19 x20 (typing_wf_local cf x18 x20 b b_ty t4) n b b_ty b' s3
          b'_ty p_UU0393_ t3
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 b_ty (Coq_tSort s3) t3) t4
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 b b_ty t4) t5
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 (snoc x20 (Env.vdef n b b_ty)) b' b'_ty t5)
      | Coq_type_App (t3, l, t_ty, t', t4, t5) ->
        x6 x18 x19 x20 wf_UU0393_ t3 l t_ty t' t4
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 t3 t_ty t4) __ __ t5
          (let x25 = fun _UU0393_0 _ t6 t7 hty -> x23 _UU0393_0 t6 t7 hty in
           let rec f _UU0393_0 _ _ _ t6 wf_UU0393_0 x26 =
             match t6 with
             | Coq_type_spine_nil ty0 -> Forall_type_spine_nil ty0
             | Coq_type_spine_cons (hd, tl, na, a, b, s3, t7, b', t8, c, t9,
                                    t10) ->
               Forall_type_spine_cons (hd, tl, na, a, b, s3, t7, b', t10, t8,
                 c, t9,
                 (let x27 = fun _UU0393_1 x27 t11 t12 hty ->
                    let Coq_pair (_, x28) = x26 _UU0393_1 x27 t11 t12 hty __
                    in
                    x28
                  in
                  Obj.magic x27 _UU0393_0 wf_UU0393_0 (Coq_tProd (na, a, b))
                    (Coq_tSort s3) t8),
                 (let x27 = fun _UU0393_1 x27 t11 t12 hty ->
                    let Coq_pair (_, x28) = x26 _UU0393_1 x27 t11 t12 hty __
                    in
                    x28
                  in
                  Obj.magic x27 _UU0393_0 wf_UU0393_0 hd a t9),
                 (f _UU0393_0 (subst1 hd O b) tl b' t10 wf_UU0393_0
                   (fun _UU0393_1 x27 t11 t12 hty _ ->
                   x26 _UU0393_1 x27 t11 t12 hty __)))
           in f x20 t_ty l t' t5 wf_UU0393_ (fun _UU0393_0 x26 t6 t7 hty _ ->
                x25 _UU0393_0 x26 t6 t7 hty))
      | Coq_type_Const (cst, u, a, decl) ->
        x7 x18 x19 x20 a cst u decl
          (let x25 = fun _ ->
             Obj.magic x23 Coq_nil (Coq_tSort Universe.Coq_lProp) (Coq_tSort
               Universe.type1) (type_Prop cf x18)
           in
           let x26 = x25 __ in let Coq_pair (x27, _) = x26 in x27) p_UU0393_
          __ __
      | Coq_type_Ind (ind, u, a, mdecl, idecl) ->
        x8 x18 x19 x20 a ind u mdecl idecl __
          (let x25 = fun _ ->
             Obj.magic x23 Coq_nil (Coq_tSort Universe.Coq_lProp) (Coq_tSort
               Universe.type1) (type_Prop cf x18)
           in
           let x26 = x25 __ in let Coq_pair (x27, _) = x26 in x27) p_UU0393_
          __
      | Coq_type_Construct (ind, i, u, a, mdecl, idecl, cdecl) ->
        x9 x18 x19 x20 a ind i u mdecl idecl cdecl __
          (let x25 = fun _ ->
             Obj.magic x23 Coq_nil (Coq_tSort Universe.Coq_lProp) (Coq_tSort
               Universe.type1) (type_Prop cf x18)
           in
           let x26 = x25 __ in let Coq_pair (x27, _) = x26 in x27) p_UU0393_
          __
      | Coq_type_Case (ci, p, c, brs, indices, ps, mdecl, idecl, a, x25, x26,
                       x27, x28) ->
        let predctx = case_predicate_context ci.ci_ind mdecl idecl p in
        x10 x18 x19 x20
          (typing_wf_local cf x18 x20 c
            (mkApps (Coq_tInd (ci.ci_ind, p.puinst)) (app p.pparams indices))
            x27) ci p c brs indices ps mdecl idecl __
          (let Coq_pair (x29, _) =
             Obj.magic x23 x20 c
               (mkApps (Coq_tInd (ci.ci_ind, p.puinst))
                 (app p.pparams indices)) x27
           in
           x29) p_UU0393_ __ a __ __
          (let x29 = fun _UU0393_' t3 t4 hty ->
             let Coq_pair (_, x29) = x23 _UU0393_' t3 t4 hty in x29
           in
           let l = app p.pparams indices in
           let c0 =
             List.rev
               (subst_instance Env.subst_instance_context p.puinst
                 (Env.app_context (Env.ind_params mdecl)
                   (Env.ind_indices idecl)))
           in
           let rec f _ _ c1 iH0 =
             match c1 with
             | Coq_ctx_inst_nil -> Coq_ctx_inst_nil
             | Coq_ctx_inst_ass (na, t3, i, inst, _UU0394_, t4, c2) ->
               Coq_ctx_inst_ass (na, t3, i, inst, _UU0394_, (Coq_pair (t4,
                 (Obj.magic iH0 x20 i t3 t4 __))),
                 (f inst
                   (Env.subst_telescope (Coq_cons (i, Coq_nil)) O _UU0394_)
                   c2 (fun _UU0393_' t5 t6 hty _ ->
                   iH0 _UU0393_' t5 t6 hty __)))
             | Coq_ctx_inst_def (na, b, t3, inst, _UU0394_, c2) ->
               Coq_ctx_inst_def (na, b, t3, inst, _UU0394_,
                 (f inst
                   (Env.subst_telescope (Coq_cons (b, Coq_nil)) O _UU0394_)
                   c2 (fun _UU0393_' t4 t5 hty _ ->
                   iH0 _UU0393_' t4 t5 hty __)))
           in f l c0 x25 (fun _UU0393_' t3 t4 hty _ ->
                x29 _UU0393_' t3 t4 hty)) x26
          (let Coq_pair (_, x29) =
             Obj.magic x23 (Env.app_context x20 predctx) p.preturn (Coq_tSort
               ps) x26
           in
           x29)
          (x24 (Env.app_context x20 predctx) p.preturn (Coq_tSort ps) x26) __
          x27
          (let Coq_pair (_, x29) =
             Obj.magic x23 x20 c
               (mkApps (Coq_tInd (ci.ci_ind, p.puinst))
                 (app p.pparams indices)) x27
           in
           x29) __
          (let l = Env.ind_ctors idecl in
           let n = O in
           let rec f n0 _ _ a0 x29 =
             match a0 with
             | All2i_nil -> All2i_nil
             | All2i_cons (x30, y, l0, r, y0, a1) ->
               let Coq_pair (p1, t3) = y0 in
               let Coq_pair (a2, t4) = p1 in
               All2i_cons (x30, y, l0, r, (Coq_pair ((Coq_pair (a2, (Coq_pair
               (t4,
               (let Coq_pair (_, x31) =
                  Obj.magic x29
                    (Env.app_context x20
                      (case_branch_context_gen ci.ci_ind mdecl p.pparams
                        p.puinst y.bcontext x30)) y.bbody
                    (mkApps
                      (lift (length (Env.cstr_args x30)) O
                        (Env.it_mkLambda_or_LetIn
                          (case_predicate_context ci.ci_ind mdecl idecl p)
                          p.preturn))
                      (app
                        (map
                          (subst (List.rev p.pparams)
                            (length (Env.cstr_args x30)))
                          (map
                            (Env.expand_lets_k
                              (subst_instance Env.subst_instance_context
                                p.puinst (Env.ind_params mdecl))
                              (length (Env.cstr_args x30)))
                            (map
                              (subst
                                (inds ci.ci_ind.inductive_mind p.puinst
                                  (Env.ind_bodies mdecl))
                                (Nat.add (length (Env.ind_params mdecl))
                                  (length (Env.cstr_args x30))))
                              (map
                                (subst_instance subst_instance_constr
                                  p.puinst) (Env.cstr_indices x30)))))
                        (Coq_cons
                        ((mkApps (Coq_tConstruct (ci.ci_ind, n0, p.puinst))
                           (app
                             (map (lift (length (Env.cstr_args x30)) O)
                               p.pparams)
                             (Env.to_extended_list (Env.cstr_args x30)))),
                        Coq_nil)))) t4 __
                in
                x31))))), (Coq_pair (t3,
               (let Coq_pair (_, x31) =
                  Obj.magic x29
                    (Env.app_context x20
                      (case_branch_context_gen ci.ci_ind mdecl p.pparams
                        p.puinst y.bcontext x30))
                    (mkApps
                      (lift (length (Env.cstr_args x30)) O
                        (Env.it_mkLambda_or_LetIn
                          (case_predicate_context ci.ci_ind mdecl idecl p)
                          p.preturn))
                      (app
                        (map
                          (subst (List.rev p.pparams)
                            (length (Env.cstr_args x30)))
                          (map
                            (Env.expand_lets_k
                              (subst_instance Env.subst_instance_context
                                p.puinst (Env.ind_params mdecl))
                              (length (Env.cstr_args x30)))
                            (map
                              (subst
                                (inds ci.ci_ind.inductive_mind p.puinst
                                  (Env.ind_bodies mdecl))
                                (Nat.add (length (Env.ind_params mdecl))
                                  (length (Env.cstr_args x30))))
                              (map
                                (subst_instance subst_instance_constr
                                  p.puinst) (Env.cstr_indices x30)))))
                        (Coq_cons
                        ((mkApps (Coq_tConstruct (ci.ci_ind, n0, p.puinst))
                           (app
                             (map (lift (length (Env.cstr_args x30)) O)
                               p.pparams)
                             (Env.to_extended_list (Env.cstr_args x30)))),
                        Coq_nil)))) (Coq_tSort ps) t3 __
                in
                x31))))),
               (f (S n0) l0 r a1 (fun _UU0393_0 t5 t6 hty _ ->
                 x29 _UU0393_0 t5 t6 hty __)))
           in f n l brs x28 (fun _UU0393_0 t3 t4 hty _ ->
                x23 _UU0393_0 t3 t4 hty))
      | Coq_type_Proj (p, c, u, mdecl, idecl, cdecl, pdecl, args, t3) ->
        x11 x18 x19 x20
          (typing_wf_local cf x18 x20 c
            (mkApps (Coq_tInd (p.proj_ind, u)) args) t3) p c u mdecl idecl
          cdecl pdecl __ args
          (let x25 = fun _ ->
             Obj.magic x23 Coq_nil (Coq_tSort Universe.Coq_lProp) (Coq_tSort
               Universe.type1) (type_Prop cf x18)
           in
           let x26 = x25 __ in let Coq_pair (x27, _) = x26 in x27) p_UU0393_
          t3
          (let x25 = fun _UU0393_0 t4 t5 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t4 t5 hty in x25
           in
           Obj.magic x25 x20 c (mkApps (Coq_tInd (p.proj_ind, u)) args) t3) __
      | Coq_type_Fix (mfix, n, decl, a, a0, a1) ->
        Obj.magic x12 x18 x19 x20 a mfix n decl __ __ p_UU0393_
          (let x25 = fun t3 t4 hty -> x23 x20 t3 t4 hty in
           let rec f _ a2 x26 =
             match a2 with
             | All_nil -> All_nil
             | All_cons (x27, l, y, a3) ->
               All_cons (x27, l,
                 (let Coq_existT (x28, t3) = y in
                  Coq_existT (x28, (Coq_pair (t3,
                  (let Coq_pair (_, x29) =
                     Obj.magic x26 x27.dtype (Coq_tSort x28) t3 __
                   in
                   x29))))), (f l a3 (fun t3 t4 hty _ -> x26 t3 t4 hty __)))
           in f mfix a0 (fun t3 t4 hty _ -> x25 t3 t4 hty))
          (let x25 = fun _UU0393_0 _ t3 t4 hty -> x23 _UU0393_0 t3 t4 hty in
           let mfixcontext = fix_context mfix in
           let rec f _ a2 x26 =
             match a2 with
             | All_nil -> All_nil
             | All_cons (x27, l, y, a3) ->
               All_cons (x27, l, (Coq_pair (y,
                 (let Coq_pair (_, x28) =
                    Obj.magic x26 (Env.app_context x20 mfixcontext)
                      (typing_wf_local cf x18
                        (Env.app_context x20 mfixcontext) x27.dbody
                        (lift (length mfixcontext) O x27.dtype) y) x27.dbody
                      (lift (length mfixcontext) O x27.dtype) y __
                  in
                  x28))),
                 (f l a3 (fun _UU0393_0 x28 t3 t4 hty _ ->
                   x26 _UU0393_0 x28 t3 t4 hty __)))
           in f mfix a1 (fun _UU0393_0 x26 t3 t4 hty _ ->
                x25 _UU0393_0 x26 t3 t4 hty)) __
      | Coq_type_CoFix (mfix, n, decl, a, a0, a1) ->
        Obj.magic x13 x18 x19 x20 a mfix n decl __ __ p_UU0393_
          (let x25 = fun t3 t4 hty -> x23 x20 t3 t4 hty in
           let rec f _ a2 x26 =
             match a2 with
             | All_nil -> All_nil
             | All_cons (x27, l, y, a3) ->
               All_cons (x27, l,
                 (let Coq_existT (x28, t3) = y in
                  Coq_existT (x28, (Coq_pair (t3,
                  (let Coq_pair (_, x29) =
                     Obj.magic x26 x27.dtype (Coq_tSort x28) t3 __
                   in
                   x29))))), (f l a3 (fun t3 t4 hty _ -> x26 t3 t4 hty __)))
           in f mfix a0 (fun t3 t4 hty _ -> x25 t3 t4 hty))
          (let x25 = fun _UU0393_0 _ t3 t4 hty -> x23 _UU0393_0 t3 t4 hty in
           let mfixcontext = fix_context mfix in
           let rec f _ a2 x26 =
             match a2 with
             | All_nil -> All_nil
             | All_cons (x27, l, y, a3) ->
               All_cons (x27, l, (Coq_pair (y,
                 (let Coq_pair (_, x28) =
                    Obj.magic x26 (Env.app_context x20 mfixcontext)
                      (typing_wf_local cf x18
                        (Env.app_context x20 mfixcontext) x27.dbody
                        (lift (length mfixcontext) O x27.dtype) y) x27.dbody
                      (lift (length mfixcontext) O x27.dtype) y __
                  in
                  x28))),
                 (f l a3 (fun _UU0393_0 x28 t3 t4 hty _ ->
                   x26 _UU0393_0 x28 t3 t4 hty __)))
           in f mfix a1 (fun _UU0393_0 x26 t3 t4 hty _ ->
                x25 _UU0393_0 x26 t3 t4 hty)) __
      | Coq_type_Int (p, prim_ty, cdecl, a, p1) ->
        x14 x18 x19 x20 a p prim_ty cdecl p_UU0393_ __ __ p1
      | Coq_type_Float (p, prim_ty, cdecl, a, p1) ->
        x15 x18 x19 x20 a p prim_ty cdecl p_UU0393_ __ __ p1
      | Coq_type_Conv (t3, a, b, s3, t4, t5, c) ->
        x16 x18 x19 x20 (typing_wf_local cf x18 x20 b (Coq_tSort s3) t5) t3 a
          b s3 p_UU0393_ t4
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 t3 a t4) t5
          (let x25 = fun _UU0393_0 t6 t7 hty ->
             let Coq_pair (_, x25) = x23 _UU0393_0 t6 t7 hty in x25
           in
           Obj.magic x25 x20 b (Coq_tSort s3) t5) c))))
  in
  Obj.magic p0 h0 (Coq_existT (_UU03a3_, (Coq_existT (wf_UU03a3_, (Coq_existT
    (_UU0393_, (Coq_existT (t0, (Coq_existT (t1, ty))))))))))

(** val nth_error_All_local_env :
    term context_decl list -> nat -> 'a1 coq_All_local_env -> (term
    context_decl, 'a1 on_local_decl) on_some **)

let rec nth_error_All_local_env _ n = function
| Coq_localenv_nil ->
  (match n with
   | O -> Obj.magic __ __
   | S x0 -> Obj.magic __ x0 __)
| Coq_localenv_cons_abs (_UU0393_, _, _, a, t0) ->
  (match n with
   | O -> Obj.magic t0
   | S n0 -> nth_error_All_local_env _UU0393_ n0 a)
| Coq_localenv_cons_def (_UU0393_, _, _, _, a, _, t0) ->
  (match n with
   | O -> Obj.magic t0
   | S n0 -> nth_error_All_local_env _UU0393_ n0 a)

(** val lookup_on_global_env :
    checker_flags -> Env.global_env -> kername -> Env.global_decl -> ('a1,
    'a2) on_global_env -> (Env.global_env_ext, (('a1, 'a2) on_global_env,
    (Env.strictly_extends_decls, ('a1, 'a2) on_global_decl) prod) prod) sigT **)

let lookup_on_global_env _ _UU03a3_ c _ x =
  let { Env.universes = universes0; Env.declarations = declarations0;
    Env.retroknowledge = retroknowledge0 } = _UU03a3_
  in
  let Coq_pair (_, o) = x in
  let rec f _ = function
  | Coq_globenv_nil -> (fun _ -> assert false (* absurd case *))
  | Coq_globenv_decl (_UU03a3_0, kn, d, o1, o2) ->
    let udecl0 = TemplateLookup.universes_decl_of_decl d in
    let _evar_0_ = fun _ _ -> Coq_existT ((Coq_pair ({ Env.universes =
      universes0; Env.declarations = _UU03a3_0; Env.retroknowledge =
      retroknowledge0 }, udecl0)), (Coq_pair ((Coq_pair (__, o1)), (Coq_pair
      ((Times3 (__, (Coq_existT ((Coq_cons ((Coq_pair (kn, d)), Coq_nil)),
      __)), __)), o2)))))
    in
    let _evar_0_0 = fun _ _ ->
      let s = f _UU03a3_0 o1 __ in
      let Coq_existT (x0, p) = s in
      let Coq_pair (p0, p1) = p in
      let Coq_pair (s0, o3) = p1 in
      let Times3 (_, s1, _) = s0 in
      Coq_existT (x0, (Coq_pair (p0, (Coq_pair ((Times3 (__,
      (let Coq_existT (x1, _) = s1 in
       Coq_existT ((Coq_cons ((Coq_pair (kn, d)), x1)), __)), __)), o3)))))
    in
    (match eqb_specT Kername.reflect_kername c kn with
     | ReflectT -> _evar_0_ __
     | ReflectF -> _evar_0_0 __)
  in f declarations0 o __

(** val coq_All_local_env_app_inv :
    Env.context -> Env.context -> 'a1 coq_All_local_env -> ('a1
    coq_All_local_env, 'a1 coq_All_local_env) prod **)

let rec coq_All_local_env_app_inv l = function
| Coq_nil -> (fun x -> Coq_pair (x, Coq_localenv_nil))
| Coq_cons (_, l0) ->
  let iHl' = coq_All_local_env_app_inv l l0 in
  (fun x -> Coq_pair
  ((match x with
    | Coq_localenv_nil -> assert false (* absurd case *)
    | Coq_localenv_cons_abs (_, _, _, x0, _) ->
      let x1 = iHl' x0 in let Coq_pair (a, _) = x1 in a
    | Coq_localenv_cons_def (_, _, _, _, x0, _, _) ->
      let Coq_pair (x1, _) = iHl' x0 in x1),
  (match x with
   | Coq_localenv_nil -> assert false (* absurd case *)
   | Coq_localenv_cons_abs (_, na, t0, x0, x1) ->
     Coq_localenv_cons_abs (l0, na, t0,
       (let Coq_pair (_, x2) = iHl' x0 in x2), x1)
   | Coq_localenv_cons_def (_, na, b, t0, x0, x1, x2) ->
     Coq_localenv_cons_def (l0, na, b, t0,
       (let Coq_pair (_, x3) = iHl' x0 in x3), x1, x2))))

(** val coq_All_local_env_lookup :
    Env.context -> nat -> term context_decl -> 'a1 coq_All_local_env -> 'a1
    on_local_decl **)

let coq_All_local_env_lookup _UU0393_ n decl x =
  let rec f _ a n0 decl0 =
    match a with
    | Coq_localenv_nil -> (fun _ -> assert false (* absurd case *))
    | Coq_localenv_cons_abs (_UU0393_0, _, _, a0, t0) ->
      (match n0 with
       | O -> (fun _ -> Obj.magic t0)
       | S n1 -> f _UU0393_0 a0 n1 decl0)
    | Coq_localenv_cons_def (_UU0393_0, _, _, _, a0, _, t0) ->
      (match n0 with
       | O -> (fun _ -> Obj.magic t0)
       | S n1 -> f _UU0393_0 a0 n1 decl0)
  in f _UU0393_ x n decl __

(** val coq_All_local_env_app :
    checker_flags -> Env.context -> Env.context -> ('a1 coq_All_local_env,
    'a1 coq_All_local_env) prod -> 'a1 coq_All_local_env **)

let rec coq_All_local_env_app h l l' x =
  match l' with
  | Coq_nil -> let Coq_pair (a, _) = x in a
  | Coq_cons (y, l0) ->
    let Coq_pair (a, b) = x in
    let x0 = fun x0 x1 -> coq_All_local_env_app h l l0 (Coq_pair (x0, x1)) in
    let x1 = x0 a in
    let { decl_name = decl_name0; decl_body = decl_body0; decl_type =
      decl_type0 } = y
    in
    (match decl_body0 with
     | Some t0 ->
       (match b with
        | Coq_localenv_cons_def (_, _, _, _, x2, x3, x4) ->
          Coq_localenv_cons_def ((Env.app_context l l0), decl_name0, t0,
            decl_type0, (x1 x2), x3, x4)
        | _ -> assert false (* absurd case *))
     | None ->
       (match b with
        | Coq_localenv_cons_abs (_, _, _, x2, x3) ->
          Coq_localenv_cons_abs ((Env.app_context l l0), decl_name0,
            decl_type0, (x1 x2), x3)
        | _ -> assert false (* absurd case *)))

(** val coq_All_local_env_map :
    checker_flags -> (term -> term) -> Env.context -> 'a1 coq_All_local_env
    -> 'a1 coq_All_local_env **)

let rec coq_All_local_env_map h f _ = function
| Coq_localenv_nil -> Coq_localenv_nil
| Coq_localenv_cons_abs (_UU0393_, na, t0, a, t1) ->
  Coq_localenv_cons_abs
    ((let rec map0 = function
      | Coq_nil -> Coq_nil
      | Coq_cons (a0, t2) -> Coq_cons ((map_decl f a0), (map0 t2))
      in map0 _UU0393_), (Env.vass na t0).decl_name,
    (f (Env.vass na t0).decl_type), (coq_All_local_env_map h f _UU0393_ a),
    t1)
| Coq_localenv_cons_def (_UU0393_, na, b, t0, a, t1, t2) ->
  Coq_localenv_cons_def
    ((let rec map0 = function
      | Coq_nil -> Coq_nil
      | Coq_cons (a0, t3) -> Coq_cons ((map_decl f a0), (map0 t3))
      in map0 _UU0393_), (Env.vdef na b t0).decl_name, (f b),
    (f (Env.vdef na b t0).decl_type), (coq_All_local_env_map h f _UU0393_ a),
    t1, t2)

(** val lookup_wf_local :
    Env.context -> 'a1 coq_All_local_env -> nat -> 'a1 coq_All_local_env **)

let rec lookup_wf_local _ a n =
  match a with
  | Coq_localenv_nil -> Coq_localenv_nil
  | Coq_localenv_cons_abs (_UU0393_, _, _, a0, _) ->
    (match n with
     | O -> a0
     | S n0 -> lookup_wf_local _UU0393_ a0 n0)
  | Coq_localenv_cons_def (_UU0393_, _, _, _, a0, _, _) ->
    (match n with
     | O -> a0
     | S n0 -> lookup_wf_local _UU0393_ a0 n0)

(** val lookup_wf_local_decl :
    Env.context -> 'a1 coq_All_local_env -> nat -> term context_decl -> ('a1
    coq_All_local_env, 'a1 on_local_decl) sigT **)

let rec lookup_wf_local_decl _ a n decl =
  match a with
  | Coq_localenv_nil -> assert false (* absurd case *)
  | Coq_localenv_cons_abs (_UU0393_, _, _, a0, t0) ->
    (match n with
     | O -> Coq_existT (a0, (Obj.magic t0))
     | S n0 -> lookup_wf_local_decl _UU0393_ a0 n0 decl)
  | Coq_localenv_cons_def (_UU0393_, _, _, _, a0, _, t0) ->
    (match n with
     | O -> Coq_existT (a0, (Obj.magic t0))
     | S n0 -> lookup_wf_local_decl _UU0393_ a0 n0 decl)

type 'p on_wf_local_decl = __

(** val nth_error_All_local_env_over :
    checker_flags -> Env.global_env_ext -> term context_decl list -> nat ->
    term context_decl -> typing lift_typing coq_All_local_env -> (typing,
    'a1) coq_All_local_env_over -> ((typing, 'a1) coq_All_local_env_over, 'a1
    on_wf_local_decl) prod **)

let rec nth_error_All_local_env_over h _UU03a3_ _ n decl _ = function
| Coq_localenv_over_nil -> assert false (* absurd case *)
| Coq_localenv_over_cons_abs (_UU0393_, _, _, all, a, _, hs) ->
  (match n with
   | O -> Coq_pair (a, (Obj.magic hs))
   | S n0 -> nth_error_All_local_env_over h _UU03a3_ _UU0393_ n0 decl all a)
| Coq_localenv_over_cons_def (_UU0393_, _, _, _, all, _, a, hc, _, _) ->
  (match n with
   | O -> Coq_pair (a, (Obj.magic hc))
   | S n0 -> nth_error_All_local_env_over h _UU03a3_ _UU0393_ n0 decl all a)

(** val wf_ext_wf : checker_flags -> Env.global_env_ext -> wf_ext -> wf **)

let wf_ext_wf _ _ =
  fst
