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
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val global_variance_gen :
    (kername -> Env.global_decl option) -> global_reference -> nat ->
    Variance.t list option **)

let global_variance_gen lookup gr napp =
  match gr with
  | IndRef ind ->
    (match lookup_inductive_gen lookup ind with
     | Some p ->
       let Coq_pair (mdecl, idecl) = p in
       (match destArity Coq_nil (Env.ind_type idecl) with
        | Some p0 ->
          let Coq_pair (ctx, _) = p0 in
          (match PeanoNat.Nat.leb (Env.context_assumptions ctx) napp with
           | Coq_true -> Env.ind_variance mdecl
           | Coq_false -> None)
        | None -> None)
     | None -> None)
  | ConstructRef (ind, k) ->
    (match lookup_constructor_gen lookup ind k with
     | Some p ->
       let Coq_pair (p0, cdecl) = p in
       let Coq_pair (mdecl, _) = p0 in
       (match PeanoNat.Nat.leb
                (Nat.add (Env.cstr_arity cdecl) (Env.ind_npars mdecl)) napp with
        | Coq_true -> Some Coq_nil
        | Coq_false -> None)
     | None -> None)
  | _ -> None

type ('eq_term, 'leq_term) compare_decls =
| Coq_compare_vass of name binder_annot * term * name binder_annot * 
   term * 'leq_term
| Coq_compare_vdef of name binder_annot * term * term * name binder_annot
   * term * term * 'eq_term * 'leq_term

(** val compare_decls_rect :
    (name binder_annot -> term -> name binder_annot -> term -> __ -> 'a2 ->
    'a3) -> (name binder_annot -> term -> term -> name binder_annot -> term
    -> term -> __ -> 'a1 -> 'a2 -> 'a3) -> term context_decl -> term
    context_decl -> ('a1, 'a2) compare_decls -> 'a3 **)

let compare_decls_rect f f0 _ _ = function
| Coq_compare_vass (na, t0, na', t', l) -> f na t0 na' t' __ l
| Coq_compare_vdef (na, b, t0, na', b', t', e, l) ->
  f0 na b t0 na' b' t' __ e l

(** val compare_decls_rec :
    (name binder_annot -> term -> name binder_annot -> term -> __ -> 'a2 ->
    'a3) -> (name binder_annot -> term -> term -> name binder_annot -> term
    -> term -> __ -> 'a1 -> 'a2 -> 'a3) -> term context_decl -> term
    context_decl -> ('a1, 'a2) compare_decls -> 'a3 **)

let compare_decls_rec f f0 _ _ = function
| Coq_compare_vass (na, t0, na', t', l) -> f na t0 na' t' __ l
| Coq_compare_vdef (na, b, t0, na', b', t', e, l) ->
  f0 na b t0 na' b' t' __ e l

type ('eq_term, 'leq_term) compare_decls_sig =
  ('eq_term, 'leq_term) compare_decls

(** val compare_decls_sig_pack :
    term context_decl -> term context_decl -> ('a1, 'a2) compare_decls ->
    (term context_decl * term context_decl) * ('a1, 'a2) compare_decls **)

let compare_decls_sig_pack x x0 compare_decls_var =
  (x,x0),compare_decls_var

(** val compare_decls_Signature :
    term context_decl -> term context_decl -> (('a1, 'a2) compare_decls, term
    context_decl * term context_decl, ('a1, 'a2) compare_decls_sig)
    coq_Signature **)

let compare_decls_Signature x x0 compare_decls_var =
  (x,x0),compare_decls_var

(** val coq_NoConfusionPackage_compare_decls :
    ((term context_decl * term context_decl) * ('a1, 'a2) compare_decls)
    coq_NoConfusionPackage **)

let coq_NoConfusionPackage_compare_decls =
  Build_NoConfusionPackage

(** val alpha_eq_subst_context :
    term context_decl list -> term context_decl list -> term list -> nat ->
    (term context_decl, term context_decl, (__, __) compare_decls) coq_All2
    -> (term context_decl, term context_decl, (__, __) compare_decls) coq_All2 **)

let rec alpha_eq_subst_context _ _ s k = function
| All2_nil -> All2_nil
| All2_cons (x0, y, l, l', y0, a) ->
  All2_cons ((map_decl (subst s (Nat.add (length l) k)) x0),
    (map_decl (subst s (Nat.add (length l') k)) y),
    (fold_context_k (fun k' -> subst s (Nat.add k' k)) l),
    (fold_context_k (fun k' -> subst s (Nat.add k' k)) l'),
    (match y0 with
     | Coq_compare_vass (na, _, na', t', _) ->
       Coq_compare_vass ((Env.vass na t').decl_name,
         (subst s (Nat.add (length l) k) (Env.vass na t').decl_type),
         (Env.vass na' t').decl_name,
         (subst s (Nat.add (length l') k) (Env.vass na' t').decl_type), __)
     | Coq_compare_vdef (na, _, _, na', b', t', _, _) ->
       Coq_compare_vdef ((Env.vdef na b' t').decl_name,
         (subst s (Nat.add (length l) k) b'),
         (subst s (Nat.add (length l) k) (Env.vdef na b' t').decl_type),
         (Env.vdef na' b' t').decl_name,
         (subst s (Nat.add (length l') k) b'),
         (subst s (Nat.add (length l') k) (Env.vdef na' b' t').decl_type),
         __, __)), (alpha_eq_subst_context l l' s k a))

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

(** val eq_term_upto_univ_napp_rect :
    Env.global_env -> (__ -> nat -> nat -> 'a1) -> (__ -> nat -> nat -> term
    list -> term list -> (term, term, eq_term_upto_univ_napp) coq_All2 ->
    'a1) -> (__ -> nat -> ident -> 'a1) -> (__ -> nat -> Universe.t ->
    Universe.t -> __ -> 'a1) -> (__ -> nat -> term -> term -> term list ->
    term list -> eq_term_upto_univ_napp -> 'a1 -> (term, term,
    eq_term_upto_univ_napp) coq_All2 -> 'a1) -> (__ -> nat -> kername ->
    Level.t list -> Level.t list -> __ -> 'a1) -> (__ -> nat -> inductive ->
    Level.t list -> Level.t list -> __ -> 'a1) -> (__ -> nat -> inductive ->
    nat -> Level.t list -> Level.t list -> __ -> 'a1) -> (__ -> nat -> name
    binder_annot -> name binder_annot -> term -> term -> term -> term -> __
    -> eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 -> 'a1)
    -> (__ -> nat -> name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> eq_term_upto_univ_napp -> 'a1 ->
    eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> name binder_annot
    -> name binder_annot -> term -> term -> term -> term -> term -> term ->
    __ -> eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 ->
    eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> case_info -> term
    predicate -> term predicate -> term -> term -> term branch list -> term
    branch list -> (term, term, eq_term_upto_univ_napp) coq_All2 -> __ ->
    eq_term_upto_univ_napp -> 'a1 -> (name binder_annot, name binder_annot,
    __) coq_All2 -> eq_term_upto_univ_napp -> 'a1 -> (term branch, term
    branch, ((name binder_annot, name binder_annot, __) coq_All2,
    eq_term_upto_univ_napp) prod) coq_All2 -> 'a1) -> (__ -> nat ->
    projection -> term -> term -> eq_term_upto_univ_napp -> 'a1 -> 'a1) ->
    (__ -> nat -> term def list -> term def list -> nat -> (term def, term
    def, (((eq_term_upto_univ_napp, eq_term_upto_univ_napp) prod, __) prod,
    __) prod) coq_All2 -> 'a1) -> (__ -> nat -> term def list -> term def
    list -> nat -> (term def, term def, (((eq_term_upto_univ_napp,
    eq_term_upto_univ_napp) prod, __) prod, __) prod) coq_All2 -> 'a1) -> (__
    -> nat -> term -> cast_kind -> term -> term -> cast_kind -> term ->
    eq_term_upto_univ_napp -> 'a1 -> __ -> eq_term_upto_univ_napp -> 'a1 ->
    'a1) -> (__ -> nat -> int -> 'a1) -> (__ -> nat -> float -> 'a1) -> nat
    -> term -> term -> eq_term_upto_univ_napp -> 'a1 **)

let rec eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 napp _ _ = function
| Coq_eq_Rel n -> f __ napp n
| Coq_eq_Evar (e0, args, args', a) -> f0 __ napp e0 args args' a
| Coq_eq_Var id -> f1 __ napp id
| Coq_eq_Sort (s, s') -> f2 __ napp s s' __
| Coq_eq_App (t0, t', u, u', e0, a) ->
  f3 __ napp t0 t' u u' e0
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 (Nat.add (length u) napp) t0 t' e0) a
| Coq_eq_Const (c, u, u') -> f4 __ napp c u u' __
| Coq_eq_Ind (i, u, u') -> f5 __ napp i u u' __
| Coq_eq_Construct (i, k, u, u') -> f6 __ napp i k u u' __
| Coq_eq_Lambda (na, na', ty, ty', t0, t', e0, e1) ->
  f7 __ napp na na' ty ty' t0 t' __ e0
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O ty ty' e0) e1
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t0 t' e1)
| Coq_eq_Prod (na, na', a, a', b, b', e0, e1) ->
  f8 __ napp na na' a a' b b' __ e0
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O a a' e0) e1
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O b b' e1)
| Coq_eq_LetIn (na, na', t0, t', ty, ty', u, u', e0, e1, e2) ->
  f9 __ napp na na' t0 t' ty ty' u u' __ e0
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t0 t' e0) e1
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O ty ty' e1) e2
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O u u' e2)
| Coq_eq_Case (ind, p, p', c, c', brs, brs', a, e0, a0, e1, a1) ->
  f10 __ napp ind p p' c c' brs brs' a __ e0
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O p.preturn p'.preturn e0) a0 e1
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O c c' e1) a1
| Coq_eq_Proj (p, c, c', e0) ->
  f11 __ napp p c c' e0
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O c c' e0)
| Coq_eq_Fix (mfix, mfix', idx, a) -> f12 __ napp mfix mfix' idx a
| Coq_eq_CoFix (mfix, mfix', idx, a) -> f13 __ napp mfix mfix' idx a
| Coq_eq_Cast (t1, c, t2, t1', c', t2', e0, e1) ->
  f14 __ napp t1 c t2 t1' c' t2' e0
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t1 t1' e0) __ e1
    (eq_term_upto_univ_napp_rect _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t2 t2' e1)
| Coq_eq_Int i -> f15 __ napp i
| Coq_eq_Float f17 -> f16 __ napp f17

(** val eq_term_upto_univ_napp_rec :
    Env.global_env -> (__ -> nat -> nat -> 'a1) -> (__ -> nat -> nat -> term
    list -> term list -> (term, term, eq_term_upto_univ_napp) coq_All2 ->
    'a1) -> (__ -> nat -> ident -> 'a1) -> (__ -> nat -> Universe.t ->
    Universe.t -> __ -> 'a1) -> (__ -> nat -> term -> term -> term list ->
    term list -> eq_term_upto_univ_napp -> 'a1 -> (term, term,
    eq_term_upto_univ_napp) coq_All2 -> 'a1) -> (__ -> nat -> kername ->
    Level.t list -> Level.t list -> __ -> 'a1) -> (__ -> nat -> inductive ->
    Level.t list -> Level.t list -> __ -> 'a1) -> (__ -> nat -> inductive ->
    nat -> Level.t list -> Level.t list -> __ -> 'a1) -> (__ -> nat -> name
    binder_annot -> name binder_annot -> term -> term -> term -> term -> __
    -> eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 -> 'a1)
    -> (__ -> nat -> name binder_annot -> name binder_annot -> term -> term
    -> term -> term -> __ -> eq_term_upto_univ_napp -> 'a1 ->
    eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> name binder_annot
    -> name binder_annot -> term -> term -> term -> term -> term -> term ->
    __ -> eq_term_upto_univ_napp -> 'a1 -> eq_term_upto_univ_napp -> 'a1 ->
    eq_term_upto_univ_napp -> 'a1 -> 'a1) -> (__ -> nat -> case_info -> term
    predicate -> term predicate -> term -> term -> term branch list -> term
    branch list -> (term, term, eq_term_upto_univ_napp) coq_All2 -> __ ->
    eq_term_upto_univ_napp -> 'a1 -> (name binder_annot, name binder_annot,
    __) coq_All2 -> eq_term_upto_univ_napp -> 'a1 -> (term branch, term
    branch, ((name binder_annot, name binder_annot, __) coq_All2,
    eq_term_upto_univ_napp) prod) coq_All2 -> 'a1) -> (__ -> nat ->
    projection -> term -> term -> eq_term_upto_univ_napp -> 'a1 -> 'a1) ->
    (__ -> nat -> term def list -> term def list -> nat -> (term def, term
    def, (((eq_term_upto_univ_napp, eq_term_upto_univ_napp) prod, __) prod,
    __) prod) coq_All2 -> 'a1) -> (__ -> nat -> term def list -> term def
    list -> nat -> (term def, term def, (((eq_term_upto_univ_napp,
    eq_term_upto_univ_napp) prod, __) prod, __) prod) coq_All2 -> 'a1) -> (__
    -> nat -> term -> cast_kind -> term -> term -> cast_kind -> term ->
    eq_term_upto_univ_napp -> 'a1 -> __ -> eq_term_upto_univ_napp -> 'a1 ->
    'a1) -> (__ -> nat -> int -> 'a1) -> (__ -> nat -> float -> 'a1) -> nat
    -> term -> term -> eq_term_upto_univ_napp -> 'a1 **)

let rec eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 napp _ _ = function
| Coq_eq_Rel n -> f __ napp n
| Coq_eq_Evar (e0, args, args', a) -> f0 __ napp e0 args args' a
| Coq_eq_Var id -> f1 __ napp id
| Coq_eq_Sort (s, s') -> f2 __ napp s s' __
| Coq_eq_App (t0, t', u, u', e0, a) ->
  f3 __ napp t0 t' u u' e0
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 (Nat.add (length u) napp) t0 t' e0) a
| Coq_eq_Const (c, u, u') -> f4 __ napp c u u' __
| Coq_eq_Ind (i, u, u') -> f5 __ napp i u u' __
| Coq_eq_Construct (i, k, u, u') -> f6 __ napp i k u u' __
| Coq_eq_Lambda (na, na', ty, ty', t0, t', e0, e1) ->
  f7 __ napp na na' ty ty' t0 t' __ e0
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O ty ty' e0) e1
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t0 t' e1)
| Coq_eq_Prod (na, na', a, a', b, b', e0, e1) ->
  f8 __ napp na na' a a' b b' __ e0
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O a a' e0) e1
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O b b' e1)
| Coq_eq_LetIn (na, na', t0, t', ty, ty', u, u', e0, e1, e2) ->
  f9 __ napp na na' t0 t' ty ty' u u' __ e0
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t0 t' e0) e1
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O ty ty' e1) e2
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O u u' e2)
| Coq_eq_Case (ind, p, p', c, c', brs, brs', a, e0, a0, e1, a1) ->
  f10 __ napp ind p p' c c' brs brs' a __ e0
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O p.preturn p'.preturn e0) a0 e1
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O c c' e1) a1
| Coq_eq_Proj (p, c, c', e0) ->
  f11 __ napp p c c' e0
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O c c' e0)
| Coq_eq_Fix (mfix, mfix', idx, a) -> f12 __ napp mfix mfix' idx a
| Coq_eq_CoFix (mfix, mfix', idx, a) -> f13 __ napp mfix mfix' idx a
| Coq_eq_Cast (t1, c, t2, t1', c', t2', e0, e1) ->
  f14 __ napp t1 c t2 t1' c' t2' e0
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t1 t1' e0) __ e1
    (eq_term_upto_univ_napp_rec _UU03a3_ f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
      f11 f12 f13 f14 f15 f16 O t2 t2' e1)
| Coq_eq_Int i -> f15 __ napp i
| Coq_eq_Float f17 -> f16 __ napp f17

type compare_term = eq_term_upto_univ_napp

(** val eq_binder_annots_refl :
    ('a1 binder_annot list, ('a1 binder_annot, 'a1 binder_annot, __)
    coq_All2) coq_Equivalence **)

let eq_binder_annots_refl =
  { coq_Equivalence_Reflexive = (fun x ->
    coq_All2_reflexivity (Obj.magic __) x); coq_Equivalence_Symmetric =
    (fun l l' h -> coq_All2_symmetry (Obj.magic __) l l' h);
    coq_Equivalence_Transitive = (fun l l' h ->
    coq_All2_transitivity (Obj.magic __) l l' h) }

(** val eq_term_upto_univ_refl :
    Env.global_env -> nat -> term -> eq_term_upto_univ_napp **)

let eq_term_upto_univ_refl _ napp t0 =
  term_forall_list_rect (fun n _ _ _ -> Coq_eq_Rel n) (fun i _ _ _ ->
    Coq_eq_Var i) (fun n l x _ _ _ -> Coq_eq_Evar (n, l, l,
    (coq_All_All2 l x (fun _ x0 -> x0 __ __ O)))) (fun s _ _ _ -> Coq_eq_Sort
    (s, s)) (fun t1 iHt1 c t2 iHt2 _ _ _ -> Coq_eq_Cast (t1, c, t2, t1, c,
    t2, (iHt1 __ __ O), (iHt2 __ __ O))) (fun n t1 iHt1 t2 iHt2 _ _ _ ->
    Coq_eq_Prod (n, n, t1, t1, t2, t2, (iHt1 __ __ O), (iHt2 __ __ O)))
    (fun n t1 iHt1 t2 iHt2 _ _ _ -> Coq_eq_Lambda (n, n, t1, t1, t2, t2,
    (iHt1 __ __ O), (iHt2 __ __ O))) (fun n t1 iHt1 t2 iHt2 t3 iHt3 _ _ _ ->
    Coq_eq_LetIn (n, n, t1, t1, t2, t2, t3, t3, (iHt1 __ __ O),
    (iHt2 __ __ O), (iHt3 __ __ O))) (fun t1 iHt l x _ _ napp0 -> Coq_eq_App
    (t1, t1, l, l, (iHt __ __ (Nat.add (length l) napp0)),
    (coq_All_All2 l x (fun _ x0 -> x0 __ __ O)))) (fun s u _ _ _ ->
    Coq_eq_Const (s, u, u)) (fun i u _ _ _ -> Coq_eq_Ind (i, u, u))
    (fun i n u _ _ _ -> Coq_eq_Construct (i, n, u, u))
    (fun ci p0 x t1 iHt l x0 _ _ _ -> Coq_eq_Case (ci, p0, p0, t1, t1, l, l,
    (let Coq_pair (a, _) = x in
     coq_All_All2 p0.pparams a (fun _ x1 -> x1 __ __ O)),
    (let Coq_pair (_, e) = x in e __ __ O),
    (reflexivity eq_binder_annots_refl.coq_Equivalence_Reflexive p0.pcontext),
    (iHt __ __ O),
    (coq_All_All2_refl l
      (coq_All_impl l x0 (fun x1 x2 -> Coq_pair
        ((reflexivity eq_binder_annots_refl.coq_Equivalence_Reflexive
           x1.bcontext), (x2 __ __ O))))))) (fun s t1 iHt _ _ _ ->
    Coq_eq_Proj (s, t1, t1, (iHt __ __ O))) (fun m n x _ _ _ -> Coq_eq_Fix
    (m, m, n,
    (coq_All_All2 m x (fun _ x0 ->
      let Coq_pair (e, e0) = x0 in
      Coq_pair ((Coq_pair ((Coq_pair ((e __ __ O), (e0 __ __ O))), __)), __)))))
    (fun m n x _ _ _ -> Coq_eq_CoFix (m, m, n,
    (coq_All_All2 m x (fun _ x0 ->
      let Coq_pair (e, e0) = x0 in
      Coq_pair ((Coq_pair ((Coq_pair ((e __ __ O), (e0 __ __ O))), __)), __)))))
    (fun i _ _ _ -> Coq_eq_Int i) (fun f _ _ _ -> Coq_eq_Float f) t0 __ __
    napp

(** val eq_term_refl :
    checker_flags -> Env.global_env -> ConstraintSet.t -> term -> compare_term **)

let eq_term_refl _ _UU03a3_ _ t0 =
  eq_term_upto_univ_refl _UU03a3_ O t0

(** val leq_term_refl :
    checker_flags -> Env.global_env -> ConstraintSet.t -> term -> compare_term **)

let leq_term_refl _ _UU03a3_ _ t0 =
  eq_term_upto_univ_refl _UU03a3_ O t0

(** val eq_term_upto_univ_morphism0 :
    Env.global_env -> term -> term -> nat -> eq_term_upto_univ_napp ->
    eq_term_upto_univ_napp **)

let rec eq_term_upto_univ_morphism0 _UU03a3_ _ _ napp = function
| Coq_eq_Evar (e, args, args', a) ->
  Coq_eq_Evar (e, args, args',
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (eq_term_upto_univ_morphism0 _UU03a3_ x0 y O y0), (f l l' a1))
     in f args args' a))
| Coq_eq_App (t0, t', u, u', e, a) ->
  Coq_eq_App (t0, t', u, u',
    (eq_term_upto_univ_morphism0 _UU03a3_ t0 t' (Nat.add (length u) napp) e),
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (eq_term_upto_univ_morphism0 _UU03a3_ x0 y O y0), (f l l' a1))
     in f u u' a))
| Coq_eq_Lambda (na, na', ty, ty', t0, t', e, e0) ->
  Coq_eq_Lambda (na, na', ty, ty', t0, t',
    (eq_term_upto_univ_morphism0 _UU03a3_ ty ty' O e),
    (eq_term_upto_univ_morphism0 _UU03a3_ t0 t' O e0))
| Coq_eq_Prod (na, na', a, a', b, b', e, e0) ->
  Coq_eq_Prod (na, na', a, a', b, b',
    (eq_term_upto_univ_morphism0 _UU03a3_ a a' O e),
    (eq_term_upto_univ_morphism0 _UU03a3_ b b' O e0))
| Coq_eq_LetIn (na, na', t0, t', ty, ty', u, u', e, e0, e1) ->
  Coq_eq_LetIn (na, na', t0, t', ty, ty', u, u',
    (eq_term_upto_univ_morphism0 _UU03a3_ t0 t' O e),
    (eq_term_upto_univ_morphism0 _UU03a3_ ty ty' O e0),
    (eq_term_upto_univ_morphism0 _UU03a3_ u u' O e1))
| Coq_eq_Case (ind, p, p', c, c', brs, brs', a, e, a0, e0, a1) ->
  Coq_eq_Case (ind, p, p', c, c', brs, brs',
    (let l = p'.pparams in
     let l0 = p.pparams in
     let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l1, l', y0, a3) ->
       All2_cons (x0, y, l1, l',
         (eq_term_upto_univ_morphism0 _UU03a3_ x0 y O y0), (f l1 l' a3))
     in f l0 l a),
    (eq_term_upto_univ_morphism0 _UU03a3_ p.preturn p'.preturn O e), a0,
    (eq_term_upto_univ_morphism0 _UU03a3_ c c' O e0),
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a3) ->
       All2_cons (x0, y, l, l',
         (let Coq_pair (a4, b) = y0 in
          Coq_pair (a4,
          (eq_term_upto_univ_morphism0 _UU03a3_ x0.bbody y.bbody O b))),
         (f l l' a3))
     in f brs brs' a1))
| Coq_eq_Proj (p, c, c', e) ->
  Coq_eq_Proj (p, c, c', (eq_term_upto_univ_morphism0 _UU03a3_ c c' O e))
| Coq_eq_Fix (mfix, mfix', idx, a) ->
  Coq_eq_Fix (mfix, mfix', idx,
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (let Coq_pair (a2, _) = y0 in
          let Coq_pair (a3, _) = a2 in
          let Coq_pair (a4, b) = a3 in
          Coq_pair ((Coq_pair ((Coq_pair
          ((eq_term_upto_univ_morphism0 _UU03a3_ x0.dtype y.dtype O a4),
          (eq_term_upto_univ_morphism0 _UU03a3_ x0.dbody y.dbody O b))),
          __)), __)), (f l l' a1))
     in f mfix mfix' a))
| Coq_eq_CoFix (mfix, mfix', idx, a) ->
  Coq_eq_CoFix (mfix, mfix', idx,
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (let Coq_pair (a2, _) = y0 in
          let Coq_pair (a3, _) = a2 in
          let Coq_pair (a4, b) = a3 in
          Coq_pair ((Coq_pair ((Coq_pair
          ((eq_term_upto_univ_morphism0 _UU03a3_ x0.dtype y.dtype O a4),
          (eq_term_upto_univ_morphism0 _UU03a3_ x0.dbody y.dbody O b))),
          __)), __)), (f l l' a1))
     in f mfix mfix' a))
| Coq_eq_Cast (t1, c, t2, t1', c', t2', e, e0) ->
  Coq_eq_Cast (t1, c, t2, t1', c', t2',
    (eq_term_upto_univ_morphism0 _UU03a3_ t1 t1' O e),
    (eq_term_upto_univ_morphism0 _UU03a3_ t2 t2' O e0))
| x0 -> x0

(** val eq_term_upto_univ_morphism :
    Env.global_env -> term -> term -> nat -> eq_term_upto_univ_napp ->
    eq_term_upto_univ_napp **)

let rec eq_term_upto_univ_morphism _UU03a3_ _ _ napp = function
| Coq_eq_Evar (e, args, args', a) ->
  Coq_eq_Evar (e, args, args',
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (eq_term_upto_univ_morphism0 _UU03a3_ x0 y O y0), (f l l' a1))
     in f args args' a))
| Coq_eq_App (t0, t', u, u', e, a) ->
  Coq_eq_App (t0, t', u, u',
    (eq_term_upto_univ_morphism _UU03a3_ t0 t' (Nat.add (length u) napp) e),
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (eq_term_upto_univ_morphism0 _UU03a3_ x0 y O y0), (f l l' a1))
     in f u u' a))
| Coq_eq_Lambda (na, na', ty, ty', t0, t', e, e0) ->
  Coq_eq_Lambda (na, na', ty, ty', t0, t',
    (eq_term_upto_univ_morphism0 _UU03a3_ ty ty' O e),
    (eq_term_upto_univ_morphism _UU03a3_ t0 t' O e0))
| Coq_eq_Prod (na, na', a, a', b, b', e, e0) ->
  Coq_eq_Prod (na, na', a, a', b, b',
    (eq_term_upto_univ_morphism0 _UU03a3_ a a' O e),
    (eq_term_upto_univ_morphism _UU03a3_ b b' O e0))
| Coq_eq_LetIn (na, na', t0, t', ty, ty', u, u', e, e0, e1) ->
  Coq_eq_LetIn (na, na', t0, t', ty, ty', u, u',
    (eq_term_upto_univ_morphism0 _UU03a3_ t0 t' O e),
    (eq_term_upto_univ_morphism0 _UU03a3_ ty ty' O e0),
    (eq_term_upto_univ_morphism _UU03a3_ u u' O e1))
| Coq_eq_Case (ind, p, p', c, c', brs, brs', a, e, a0, e0, a1) ->
  Coq_eq_Case (ind, p, p', c, c', brs, brs',
    (let l = p'.pparams in
     let l0 = p.pparams in
     let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l1, l', y0, a3) ->
       All2_cons (x0, y, l1, l',
         (eq_term_upto_univ_morphism0 _UU03a3_ x0 y O y0), (f l1 l' a3))
     in f l0 l a),
    (eq_term_upto_univ_morphism0 _UU03a3_ p.preturn p'.preturn O e), a0,
    (eq_term_upto_univ_morphism0 _UU03a3_ c c' O e0),
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a3) ->
       All2_cons (x0, y, l, l',
         (let Coq_pair (a4, e1) = y0 in
          Coq_pair (a4,
          (eq_term_upto_univ_morphism0 _UU03a3_ x0.bbody y.bbody O e1))),
         (f l l' a3))
     in f brs brs' a1))
| Coq_eq_Proj (p, c, c', e) ->
  Coq_eq_Proj (p, c, c', (eq_term_upto_univ_morphism0 _UU03a3_ c c' O e))
| Coq_eq_Fix (mfix, mfix', idx, a) ->
  Coq_eq_Fix (mfix, mfix', idx,
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (let Coq_pair (p, _) = y0 in
          let Coq_pair (p0, _) = p in
          let Coq_pair (e, e0) = p0 in
          Coq_pair ((Coq_pair ((Coq_pair
          ((eq_term_upto_univ_morphism0 _UU03a3_ x0.dtype y.dtype O e),
          (eq_term_upto_univ_morphism0 _UU03a3_ x0.dbody y.dbody O e0))),
          __)), __)), (f l l' a1))
     in f mfix mfix' a))
| Coq_eq_CoFix (mfix, mfix', idx, a) ->
  Coq_eq_CoFix (mfix, mfix', idx,
    (let rec f _ _ = function
     | All2_nil -> All2_nil
     | All2_cons (x0, y, l, l', y0, a1) ->
       All2_cons (x0, y, l, l',
         (let Coq_pair (p, _) = y0 in
          let Coq_pair (p0, _) = p in
          let Coq_pair (e, e0) = p0 in
          Coq_pair ((Coq_pair ((Coq_pair
          ((eq_term_upto_univ_morphism0 _UU03a3_ x0.dtype y.dtype O e),
          (eq_term_upto_univ_morphism0 _UU03a3_ x0.dbody y.dbody O e0))),
          __)), __)), (f l l' a1))
     in f mfix mfix' a))
| Coq_eq_Cast (t1, c, t2, t1', c', t2', e, e0) ->
  Coq_eq_Cast (t1, c, t2, t1', c', t2',
    (eq_term_upto_univ_morphism0 _UU03a3_ t1 t1' O e),
    (eq_term_upto_univ_morphism0 _UU03a3_ t2 t2' O e0))
| x0 -> x0

(** val eq_term_upto_univ_impl :
    Env.global_env -> nat -> nat -> (term, eq_term_upto_univ_napp,
    eq_term_upto_univ_napp) subrelation **)

let eq_term_upto_univ_impl _ napp napp' t0 t' =
  term_forall_list_rect (fun n _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Rel _ -> Coq_eq_Rel n
    | _ -> assert false (* absurd case *)) (fun i _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Var _ -> Coq_eq_Var i
    | _ -> assert false (* absurd case *)) (fun n l x _ _ _ _ _ _ _ _ x0 ->
    match x0 with
    | Coq_eq_Evar (_, _, args', x1) ->
      Coq_eq_Evar (n, l, args',
        (coq_All2_impl' l args' x1
          (coq_All_impl l x (fun _ x2 y x3 -> x2 __ __ O O __ __ __ y x3))))
    | _ -> assert false (* absurd case *)) (fun s _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Sort (_, s') -> Coq_eq_Sort (s, s')
    | _ -> assert false (* absurd case *))
    (fun t1 iHt1 c t2 iHt2 _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Cast (_, _, _, t1', c', t2', x0, x1) ->
      Coq_eq_Cast (t1, c, t2, t1', c', t2', (iHt1 __ __ O O __ __ __ t1' x0),
        (iHt2 __ __ O O __ __ __ t2' x1))
    | _ -> assert false (* absurd case *))
    (fun n t1 iHt1 t2 iHt2 _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Prod (_, na', _, a', _, b', x0, x1) ->
      Coq_eq_Prod (n, na', t1, a', t2, b', (iHt1 __ __ O O __ __ __ a' x0),
        (iHt2 __ __ O O __ __ __ b' x1))
    | _ -> assert false (* absurd case *))
    (fun n t1 iHt1 t2 iHt2 _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Lambda (_, na', _, ty', _, t'0, x0, x1) ->
      Coq_eq_Lambda (n, na', t1, ty', t2, t'0,
        (iHt1 __ __ O O __ __ __ ty' x0), (iHt2 __ __ O O __ __ __ t'0 x1))
    | _ -> assert false (* absurd case *))
    (fun n t1 iHt1 t2 iHt2 t3 iHt3 _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_LetIn (_, na', _, t'0, _, ty', _, u', x0, x1, x2) ->
      Coq_eq_LetIn (n, na', t1, t'0, t2, ty', t3, u',
        (iHt1 __ __ O O __ __ __ t'0 x0), (iHt2 __ __ O O __ __ __ ty' x1),
        (iHt3 __ __ O O __ __ __ u' x2))
    | _ -> assert false (* absurd case *))
    (fun t1 iHt l x _ _ napp0 napp'0 _ _ _ _ x0 ->
    match x0 with
    | Coq_eq_App (_, t'0, _, u', x1, x2) ->
      Coq_eq_App (t1, t'0, l, u',
        (iHt __ __ (Nat.add (length l) napp0) (Nat.add (length l) napp'0) __
          __ __ t'0 x1),
        (let x3 = coq_All2_All_mix_left l u' x x2 in
         coq_All2_impl l u' x3 (fun _ y x4 ->
           let Coq_pair (a, b) = x4 in a __ __ O O __ __ __ y b)))
    | _ -> assert false (* absurd case *)) (fun s u _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Const (_, _, u') -> Coq_eq_Const (s, u, u')
    | _ -> assert false (* absurd case *)) (fun i u _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Ind (_, _, u') -> Coq_eq_Ind (i, u, u')
    | _ -> assert false (* absurd case *)) (fun i n u _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Construct (_, _, _, u') -> Coq_eq_Construct (i, n, u, u')
    | _ -> assert false (* absurd case *))
    (fun ci p0 x t1 iHt l x0 _ _ _ _ _ _ _ _ x1 ->
    let Coq_pair (a, e) = x in
    (match x1 with
     | Coq_eq_Case (_, _, p', _, c', _, brs', x2, x3, x4, x5, x6) ->
       Coq_eq_Case (ci, p0, p', t1, c', l, brs',
         (coq_All2_impl' p0.pparams p'.pparams x2
           (coq_All_impl p0.pparams a (fun _ x7 y x8 ->
             x7 __ __ O O __ __ __ y x8))),
         (e __ __ O O __ __ __ p'.preturn x3), x4,
         (iHt __ __ O O __ __ __ c' x5),
         (coq_All2_impl' l brs' x6
           (coq_All_impl l x0 (fun _ x7 y x8 ->
             let Coq_pair (a0, e0) = x8 in
             Coq_pair (a0, (x7 __ __ O O __ __ __ y.bbody e0))))))
     | _ -> assert false (* absurd case *)))
    (fun s t1 iHt _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Proj (_, _, c', x0) ->
      Coq_eq_Proj (s, t1, c', (iHt __ __ O O __ __ __ c' x0))
    | _ -> assert false (* absurd case *)) (fun m n x _ _ _ _ _ _ _ _ x0 ->
    match x0 with
    | Coq_eq_Fix (_, mfix', _, x1) ->
      Coq_eq_Fix (m, mfix', n,
        (coq_All2_impl' m mfix' x1
          (coq_All_impl m x (fun _ x2 y x3 ->
            let Coq_pair (e, e0) = x2 in
            let Coq_pair (p, _) = x3 in
            let Coq_pair (p0, _) = p in
            let Coq_pair (e1, e2) = p0 in
            Coq_pair ((Coq_pair ((Coq_pair
            ((e __ __ O O __ __ __ y.dtype e1),
            (e0 __ __ O O __ __ __ y.dbody e2))), __)), __)))))
    | _ -> assert false (* absurd case *)) (fun m n x _ _ _ _ _ _ _ _ x0 ->
    match x0 with
    | Coq_eq_CoFix (_, mfix', _, x1) ->
      Coq_eq_CoFix (m, mfix', n,
        (coq_All2_impl' m mfix' x1
          (coq_All_impl m x (fun _ x2 y x3 ->
            let Coq_pair (e, e0) = x2 in
            let Coq_pair (p, _) = x3 in
            let Coq_pair (p0, _) = p in
            let Coq_pair (e1, e2) = p0 in
            Coq_pair ((Coq_pair ((Coq_pair
            ((e __ __ O O __ __ __ y.dtype e1),
            (e0 __ __ O O __ __ __ y.dbody e2))), __)), __)))))
    | _ -> assert false (* absurd case *)) (fun i _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Int _ -> Coq_eq_Int i
    | _ -> assert false (* absurd case *)) (fun f _ _ _ _ _ _ _ _ x ->
    match x with
    | Coq_eq_Float _ -> Coq_eq_Float f
    | _ -> assert false (* absurd case *)) t0 __ __ napp napp' __ __ __ t'

(** val eq_term_leq_term :
    checker_flags -> Env.global_env -> ConstraintSet.t -> term -> term ->
    compare_term -> compare_term **)

let eq_term_leq_term _ _UU03a3_ _ t0 u =
  eq_term_upto_univ_morphism _UU03a3_ t0 u O

(** val eq_term_upto_univ_mkApps :
    checker_flags -> Env.global_env -> nat -> term -> term list -> term ->
    term list -> eq_term_upto_univ_napp -> (term, term,
    eq_term_upto_univ_napp) coq_All2 -> eq_term_upto_univ_napp **)

let eq_term_upto_univ_mkApps _ _ _ f l f' _ e x =
  match l with
  | Coq_nil ->
    (match x with
     | All2_nil -> e
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y0, _, l', x0, x1) ->
       (match isApp f with
        | Coq_true ->
          (match f with
           | Coq_tApp (f0, args) ->
             (match f' with
              | Coq_tApp (f1, args0) ->
                (match e with
                 | Coq_eq_App (_, _, _, _, x2, x3) ->
                   Coq_eq_App (f0, f1, (app args (Coq_cons (y, l0))),
                     (app args0 (Coq_cons (y0, l'))), x2,
                     (coq_All2_app args (Coq_cons (y, l0)) args0 (Coq_cons
                       (y0, l')) x3 (All2_cons (y, y0, l0, l', x0, x1))))
                 | _ -> assert false (* absurd case *))
              | _ -> assert false (* absurd case *))
           | _ -> assert false (* absurd case *))
        | Coq_false ->
          Coq_eq_App (f, f', (Coq_cons (y, l0)), (Coq_cons (y0, l')), e,
            (All2_cons (y, y0, l0, l', x0, x1)))))

(** val leq_term_mkApps :
    checker_flags -> Env.global_env -> ConstraintSet.t -> term -> term list
    -> term -> term list -> compare_term -> (term, term, compare_term)
    coq_All2 -> compare_term **)

let leq_term_mkApps h _UU03a3_ _ f l f' l' x x0 =
  eq_term_upto_univ_mkApps h _UU03a3_ O f l f' l'
    (eq_term_upto_univ_impl _UU03a3_ O (Nat.add (length l) O) f f' x) x0
