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

(** val puinst : 'a1 predicate -> Instance.t **)

let puinst p =
  p.puinst

(** val pparams : 'a1 predicate -> 'a1 list **)

let pparams p =
  p.pparams

(** val pcontext : 'a1 predicate -> aname list **)

let pcontext p =
  p.pcontext

(** val preturn : 'a1 predicate -> 'a1 **)

let preturn p =
  p.preturn

(** val coq_NoConfusionPackage_predicate :
    'a1 predicate coq_NoConfusionPackage **)

let coq_NoConfusionPackage_predicate =
  Build_NoConfusionPackage

(** val predicate_eq_dec : 'a1 coq_EqDec -> 'a1 predicate coq_EqDec **)

let predicate_eq_dec x x0 y =
  let { puinst = puinst0; pparams = pparams0; pcontext = pcontext0; preturn =
    preturn0 } = x0
  in
  let { puinst = puinst1; pparams = pparams1; pcontext = pcontext1; preturn =
    preturn1 } = y
  in
  (match eq_dec_point puinst0
           (coq_EqDec_EqDecPoint
             (list_eqdec (coq_ReflectEq_EqDec Level.reflect_level)) puinst0)
           puinst1 with
   | Coq_left ->
     (match eq_dec_point pparams0
              (coq_EqDec_EqDecPoint (list_eqdec x) pparams0) pparams1 with
      | Coq_left ->
        (match eq_dec_point pcontext0
                 (coq_EqDec_EqDecPoint (list_eqdec anqme_eqdec) pcontext0)
                 pcontext1 with
         | Coq_left ->
           eq_dec_point preturn0 (coq_EqDec_EqDecPoint x preturn0) preturn1
         | Coq_right -> Coq_right)
      | Coq_right -> Coq_right)
   | Coq_right -> Coq_right)

(** val string_of_predicate :
    ('a1 -> String.t) -> 'a1 predicate -> String.t **)

let string_of_predicate f p =
  String.append (String.String (Coq_x28, String.EmptyString))
    (String.append (String.String (Coq_x28, String.EmptyString))
      (String.append
        (String.concat (String.String (Coq_x2c, String.EmptyString))
          (map f p.pparams))
        (String.append (String.String (Coq_x29, String.EmptyString))
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_universe_instance p.puinst)
              (String.append (String.String (Coq_x2c, (String.String
                (Coq_x28, String.EmptyString))))
                (String.append
                  (String.concat (String.String (Coq_x2c,
                    String.EmptyString))
                    (map
                      (let f0 = fun b -> b.binder_name in
                       fun x -> string_of_name (f0 x)) p.pcontext))
                  (String.append (String.String (Coq_x29,
                    String.EmptyString))
                    (String.append (String.String (Coq_x2c,
                      String.EmptyString))
                      (String.append (f p.preturn) (String.String (Coq_x29,
                        String.EmptyString))))))))))))

(** val test_predicate :
    (Instance.t -> bool) -> ('a1 -> bool) -> ('a1 -> bool) -> 'a1 predicate
    -> bool **)

let test_predicate instf paramf preturnf p =
  match match instf p.puinst with
        | Coq_true -> forallb paramf p.pparams
        | Coq_false -> Coq_false with
  | Coq_true -> preturnf p.preturn
  | Coq_false -> Coq_false

(** val eqb_predicate :
    (Instance.t -> Instance.t -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1
    predicate -> 'a1 predicate -> bool **)

let eqb_predicate eqb_univ_instance eqterm p p' =
  match match match forallb2 eqterm p.pparams p'.pparams with
              | Coq_true -> eqb_univ_instance p.puinst p'.puinst
              | Coq_false -> Coq_false with
        | Coq_true -> forallb2 eqb_binder_annot p.pcontext p'.pcontext
        | Coq_false -> Coq_false with
  | Coq_true -> eqterm p.preturn p'.preturn
  | Coq_false -> Coq_false

(** val map_predicate :
    (Instance.t -> Instance.t) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1
    predicate -> 'a2 predicate **)

let map_predicate uf paramf preturnf p =
  { puinst = (uf p.puinst); pparams = (map paramf p.pparams); pcontext =
    p.pcontext; preturn = (preturnf p.preturn) }

type ('term, 'pparams, 'preturn) tCasePredProp =
  (('term, 'pparams) coq_All, 'preturn) prod

(** val map_predicate_k :
    (Instance.t -> Instance.t) -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 predicate
    -> 'a1 predicate **)

let map_predicate_k uf f k p =
  { puinst = (uf p.puinst); pparams = (map (f k) p.pparams); pcontext =
    p.pcontext; preturn = (f (Nat.add (length p.pcontext) k) p.preturn) }

(** val test_predicate_k :
    (Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1 predicate ->
    bool **)

let test_predicate_k instp p k pred =
  match match instp pred.puinst with
        | Coq_true -> forallb (p k) pred.pparams
        | Coq_false -> Coq_false with
  | Coq_true -> p (Nat.add (length pred.pcontext) k) pred.preturn
  | Coq_false -> Coq_false

type 'term branch = { bcontext : aname list; bbody : 'term }

(** val bcontext : 'a1 branch -> aname list **)

let bcontext b =
  b.bcontext

(** val bbody : 'a1 branch -> 'a1 **)

let bbody b =
  b.bbody

(** val coq_NoConfusionPackage_branch : 'a1 branch coq_NoConfusionPackage **)

let coq_NoConfusionPackage_branch =
  Build_NoConfusionPackage

(** val branch_eq_dec : 'a1 coq_EqDec -> 'a1 branch coq_EqDec **)

let branch_eq_dec x x0 y =
  let { bcontext = bcontext0; bbody = bbody0 } = x0 in
  let { bcontext = bcontext1; bbody = bbody1 } = y in
  (match eq_dec_point bcontext0
           (coq_EqDec_EqDecPoint (list_eqdec anqme_eqdec) bcontext0) bcontext1 with
   | Coq_left -> eq_dec_point bbody0 (coq_EqDec_EqDecPoint x bbody0) bbody1
   | Coq_right -> Coq_right)

(** val string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t **)

let string_of_branch f b =
  String.append (String.String (Coq_x28, (String.String (Coq_x5b,
    String.EmptyString))))
    (String.append
      (String.concat (String.String (Coq_x2c, String.EmptyString))
        (map
          (let f0 = fun b0 -> b0.binder_name in fun x -> string_of_name (f0 x))
          b.bcontext))
      (String.append (String.String (Coq_x5d, (String.String (Coq_x2c,
        (String.String (Coq_x20, String.EmptyString))))))
        (String.append (f b.bbody) (String.String (Coq_x29,
          String.EmptyString)))))

(** val pretty_string_of_branch :
    ('a1 -> String.t) -> 'a1 branch -> String.t **)

let pretty_string_of_branch f b =
  String.append
    (String.concat (String.String (Coq_x20, String.EmptyString))
      (map
        (let f0 = fun b0 -> b0.binder_name in fun x -> string_of_name (f0 x))
        b.bcontext))
    (String.append (String.String (Coq_x20, (String.String (Coq_x3d,
      (String.String (Coq_x3e, (String.String (Coq_x20,
      String.EmptyString)))))))) (f b.bbody))

(** val test_branch : ('a1 -> bool) -> 'a1 branch -> bool **)

let test_branch bodyf b =
  bodyf b.bbody

(** val map_branch : ('a1 -> 'a2) -> 'a1 branch -> 'a2 branch **)

let map_branch bbodyf b =
  { bcontext = b.bcontext; bbody = (bbodyf b.bbody) }

(** val map_branches : ('a1 -> 'a2) -> 'a1 branch list -> 'a2 branch list **)

let map_branches f l =
  map (map_branch f) l

type ('a, 'p) tCaseBrsProp = ('a branch, 'p) coq_All

module Coq__1 = struct
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
include Coq__1

(** val term_rect :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
    (Universe.t -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 -> 'a1)
    -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1
    -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> term ->
    'a1 -> 'a1) -> (term -> 'a1 -> term list -> 'a1) -> (kername ->
    Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) -> (inductive ->
    nat -> Instance.t -> 'a1) -> (case_info -> term predicate -> term -> 'a1
    -> term branch list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) ->
    (term mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (int
    -> 'a1) -> (float -> 'a1) -> term -> 'a1 **)

let rec term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 = function
| Coq_tRel n -> f n
| Coq_tVar id0 -> f0 id0
| Coq_tEvar (ev, args) -> f1 ev args
| Coq_tSort s -> f2 s
| Coq_tCast (t1, kind, v) ->
  f3 t1
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 t1)
    kind v
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 v)
| Coq_tProd (na, ty, body) ->
  f4 na ty
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 ty)
    body
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      body)
| Coq_tLambda (na, ty, body) ->
  f5 na ty
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 ty)
    body
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      body)
| Coq_tLetIn (na, def, def_ty, body) ->
  f6 na def
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      def) def_ty
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      def_ty) body
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      body)
| Coq_tApp (f17, args) ->
  f7 f17
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17) args
| Coq_tConst (c, u) -> f8 c u
| Coq_tInd (ind, u) -> f9 ind u
| Coq_tConstruct (ind, idx, u) -> f10 ind idx u
| Coq_tCase (ci, type_info, discr, branches) ->
  f11 ci type_info discr
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      discr) branches
| Coq_tProj (proj, t1) ->
  f12 proj t1
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 t1)
| Coq_tFix (mfix, idx) -> f13 mfix idx
| Coq_tCoFix (mfix, idx) -> f14 mfix idx
| Coq_tInt i -> f15 i
| Coq_tFloat f17 -> f16 f17

(** val term_rec :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
    (Universe.t -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 -> 'a1)
    -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1
    -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> term ->
    'a1 -> 'a1) -> (term -> 'a1 -> term list -> 'a1) -> (kername ->
    Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) -> (inductive ->
    nat -> Instance.t -> 'a1) -> (case_info -> term predicate -> term -> 'a1
    -> term branch list -> 'a1) -> (projection -> term -> 'a1 -> 'a1) ->
    (term mfixpoint -> nat -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (int
    -> 'a1) -> (float -> 'a1) -> term -> 'a1 **)

let rec term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 = function
| Coq_tRel n -> f n
| Coq_tVar id0 -> f0 id0
| Coq_tEvar (ev, args) -> f1 ev args
| Coq_tSort s -> f2 s
| Coq_tCast (t1, kind, v) ->
  f3 t1
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 t1)
    kind v
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 v)
| Coq_tProd (na, ty, body) ->
  f4 na ty
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 ty)
    body
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      body)
| Coq_tLambda (na, ty, body) ->
  f5 na ty
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 ty)
    body
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      body)
| Coq_tLetIn (na, def, def_ty, body) ->
  f6 na def
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 def)
    def_ty
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      def_ty) body
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      body)
| Coq_tApp (f17, args) ->
  f7 f17
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17)
    args
| Coq_tConst (c, u) -> f8 c u
| Coq_tInd (ind, u) -> f9 ind u
| Coq_tConstruct (ind, idx, u) -> f10 ind idx u
| Coq_tCase (ci, type_info, discr, branches) ->
  f11 ci type_info discr
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      discr) branches
| Coq_tProj (proj, t1) ->
  f12 proj t1
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 t1)
| Coq_tFix (mfix, idx) -> f13 mfix idx
| Coq_tCoFix (mfix, idx) -> f14 mfix idx
| Coq_tInt i -> f15 i
| Coq_tFloat f17 -> f16 f17

(** val hole : term **)

let hole =
  Coq_tEvar (fresh_evar_id, Coq_nil)

(** val mkApps : term -> term list -> term **)

let mkApps t0 us = match us with
| Coq_nil -> t0
| Coq_cons (_, _) ->
  (match t0 with
   | Coq_tApp (f, args) -> Coq_tApp (f, (app args us))
   | _ -> Coq_tApp (t0, us))

(** val lift : nat -> nat -> term -> term **)

let rec lift n k t0 = match t0 with
| Coq_tRel i ->
  Coq_tRel
    (match PeanoNat.Nat.leb k i with
     | Coq_true -> Nat.add n i
     | Coq_false -> i)
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (lift n k) args))
| Coq_tCast (c, kind, t1) -> Coq_tCast ((lift n k c), kind, (lift n k t1))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (lift n k a), (lift n (S k) b))
| Coq_tLambda (na, t1, m) -> Coq_tLambda (na, (lift n k t1), (lift n (S k) m))
| Coq_tLetIn (na, b, t1, b') ->
  Coq_tLetIn (na, (lift n k b), (lift n k t1), (lift n (S k) b'))
| Coq_tApp (u, v) -> Coq_tApp ((lift n k u), (map (lift n k) v))
| Coq_tCase (ind, p, c, brs) ->
  let k' = Nat.add (length p.pcontext) k in
  let p' = map_predicate (Obj.magic id) (lift n k) (lift n k') p in
  let brs' =
    map (fun b -> map_branch (lift n (Nat.add (length b.bcontext) k)) b) brs
  in
  Coq_tCase (ind, p', (lift n k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (lift n k c))
| Coq_tFix (mfix, idx) ->
  let k' = Nat.add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = Nat.add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tCoFix (mfix', idx)
| _ -> t0

(** val subst : term list -> nat -> term -> term **)

let rec subst s k u = match u with
| Coq_tRel n ->
  (match PeanoNat.Nat.leb k n with
   | Coq_true ->
     (match nth_error s (Nat.sub n k) with
      | Some b -> lift k O b
      | None -> Coq_tRel (Nat.sub n (length s)))
   | Coq_false -> Coq_tRel n)
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst s k) args))
| Coq_tCast (c, kind, ty) -> Coq_tCast ((subst s k c), kind, (subst s k ty))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (subst s k a), (subst s (S k) b))
| Coq_tLambda (na, t0, m) ->
  Coq_tLambda (na, (subst s k t0), (subst s (S k) m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst s k b), (subst s k ty), (subst s (S k) b'))
| Coq_tApp (u0, v) -> mkApps (subst s k u0) (map (subst s k) v)
| Coq_tCase (ind, p, c, brs) ->
  let k' = Nat.add (length p.pcontext) k in
  let p' = map_predicate (Obj.magic id) (subst s k) (subst s k') p in
  let brs' =
    map (fun b -> map_branch (subst s (Nat.add (length b.bcontext) k)) b) brs
  in
  Coq_tCase (ind, p', (subst s k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (subst s k c))
| Coq_tFix (mfix, idx) ->
  let k' = Nat.add (length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = Nat.add (length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tCoFix (mfix', idx)
| _ -> u

(** val subst1 : term -> nat -> term -> term **)

let subst1 t0 k u =
  subst (Coq_cons (t0, Coq_nil)) k u

(** val closedn : nat -> term -> bool **)

let rec closedn k = function
| Coq_tRel i -> PeanoNat.Nat.ltb i k
| Coq_tEvar (_, args) -> forallb (closedn k) args
| Coq_tCast (c, _, t1) ->
  (match closedn k c with
   | Coq_true -> closedn k t1
   | Coq_false -> Coq_false)
| Coq_tProd (_, t1, m) ->
  (match closedn k t1 with
   | Coq_true -> closedn (S k) m
   | Coq_false -> Coq_false)
| Coq_tLambda (_, t1, m) ->
  (match closedn k t1 with
   | Coq_true -> closedn (S k) m
   | Coq_false -> Coq_false)
| Coq_tLetIn (_, b, t1, b') ->
  (match match closedn k b with
         | Coq_true -> closedn k t1
         | Coq_false -> Coq_false with
   | Coq_true -> closedn (S k) b'
   | Coq_false -> Coq_false)
| Coq_tApp (u, v) ->
  (match closedn k u with
   | Coq_true -> forallb (closedn k) v
   | Coq_false -> Coq_false)
| Coq_tCase (_, p, c, brs) ->
  let k' = Nat.add (length p.pcontext) k in
  let p' = test_predicate (fun _ -> Coq_true) (closedn k) (closedn k') p in
  let brs' =
    forallb (fun b ->
      test_branch (closedn (Nat.add (length b.bcontext) k)) b) brs
  in
  (match match p' with
         | Coq_true -> closedn k c
         | Coq_false -> Coq_false with
   | Coq_true -> brs'
   | Coq_false -> Coq_false)
| Coq_tProj (_, c) -> closedn k c
| Coq_tFix (mfix, _) ->
  let k' = Nat.add (length mfix) k in
  forallb (test_def (closedn k) (closedn k')) mfix
| Coq_tCoFix (mfix, _) ->
  let k' = Nat.add (length mfix) k in
  forallb (test_def (closedn k) (closedn k')) mfix
| _ -> Coq_true

(** val noccur_between : nat -> nat -> term -> bool **)

let rec noccur_between k n = function
| Coq_tRel i ->
  (match PeanoNat.Nat.ltb i k with
   | Coq_true -> PeanoNat.Nat.leb (Nat.add k n) i
   | Coq_false -> Coq_false)
| Coq_tEvar (_, args) -> forallb (noccur_between k n) args
| Coq_tCast (c, _, t1) ->
  (match noccur_between k n c with
   | Coq_true -> noccur_between k n t1
   | Coq_false -> Coq_false)
| Coq_tProd (_, t1, m) ->
  (match noccur_between k n t1 with
   | Coq_true -> noccur_between (S k) n m
   | Coq_false -> Coq_false)
| Coq_tLambda (_, t1, m) ->
  (match noccur_between k n t1 with
   | Coq_true -> noccur_between (S k) n m
   | Coq_false -> Coq_false)
| Coq_tLetIn (_, b, t1, b') ->
  (match match noccur_between k n b with
         | Coq_true -> noccur_between k n t1
         | Coq_false -> Coq_false with
   | Coq_true -> noccur_between (S k) n b'
   | Coq_false -> Coq_false)
| Coq_tApp (u, v) ->
  (match noccur_between k n u with
   | Coq_true -> forallb (noccur_between k n) v
   | Coq_false -> Coq_false)
| Coq_tCase (_, p, c, brs) ->
  let k' = Nat.add (length p.pcontext) k in
  let p' =
    test_predicate (fun _ -> Coq_true) (noccur_between k n)
      (noccur_between k' n) p
  in
  let brs' =
    forallb (fun b ->
      test_branch
        (let k0 = Nat.add (length b.bcontext) k in noccur_between k0 n) b) brs
  in
  (match match p' with
         | Coq_true -> noccur_between k n c
         | Coq_false -> Coq_false with
   | Coq_true -> brs'
   | Coq_false -> Coq_false)
| Coq_tProj (_, c) -> noccur_between k n c
| Coq_tFix (mfix, _) ->
  let k' = Nat.add (length mfix) k in
  forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
| Coq_tCoFix (mfix, _) ->
  let k' = Nat.add (length mfix) k in
  forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
| _ -> Coq_true

(** val subst_instance_constr : term coq_UnivSubst **)

let rec subst_instance_constr u c = match c with
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst_instance_constr u) args))
| Coq_tSort s -> Coq_tSort (subst_instance_univ u s)
| Coq_tCast (c0, kind, ty) ->
  Coq_tCast ((subst_instance_constr u c0), kind, (subst_instance_constr u ty))
| Coq_tProd (na, a, b) ->
  Coq_tProd (na, (subst_instance_constr u a), (subst_instance_constr u b))
| Coq_tLambda (na, t0, m) ->
  Coq_tLambda (na, (subst_instance_constr u t0), (subst_instance_constr u m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst_instance_constr u b), (subst_instance_constr u ty),
    (subst_instance_constr u b'))
| Coq_tApp (f, v) ->
  Coq_tApp ((subst_instance_constr u f), (map (subst_instance_constr u) v))
| Coq_tConst (c0, u') -> Coq_tConst (c0, (subst_instance_instance u u'))
| Coq_tInd (i, u') -> Coq_tInd (i, (subst_instance_instance u u'))
| Coq_tConstruct (ind, k, u') ->
  Coq_tConstruct (ind, k, (subst_instance_instance u u'))
| Coq_tCase (ind, p, c0, brs) ->
  let p' =
    map_predicate (subst_instance_instance u) (subst_instance_constr u)
      (subst_instance_constr u) p
  in
  let brs' = map (map_branch (subst_instance_constr u)) brs in
  Coq_tCase (ind, p', (subst_instance_constr u c0), brs')
| Coq_tProj (p, c0) -> Coq_tProj (p, (subst_instance_constr u c0))
| Coq_tFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tCoFix (mfix', idx)
| _ -> c

(** val closedu : nat -> term -> bool **)

let rec closedu k = function
| Coq_tEvar (_, args) -> forallb (closedu k) args
| Coq_tSort univ -> closedu_universe k univ
| Coq_tCast (c, _, t1) ->
  (match closedu k c with
   | Coq_true -> closedu k t1
   | Coq_false -> Coq_false)
| Coq_tProd (_, t1, m) ->
  (match closedu k t1 with
   | Coq_true -> closedu k m
   | Coq_false -> Coq_false)
| Coq_tLambda (_, t1, m) ->
  (match closedu k t1 with
   | Coq_true -> closedu k m
   | Coq_false -> Coq_false)
| Coq_tLetIn (_, b, t1, b') ->
  (match match closedu k b with
         | Coq_true -> closedu k t1
         | Coq_false -> Coq_false with
   | Coq_true -> closedu k b'
   | Coq_false -> Coq_false)
| Coq_tApp (u, v) ->
  (match closedu k u with
   | Coq_true -> forallb (closedu k) v
   | Coq_false -> Coq_false)
| Coq_tConst (_, u) -> closedu_instance k u
| Coq_tInd (_, u) -> closedu_instance k u
| Coq_tConstruct (_, _, u) -> closedu_instance k u
| Coq_tCase (_, p, c, brs) ->
  let p' = test_predicate (closedu_instance k) (closedu k) (closedu k) p in
  let brs' = forallb (test_branch (closedu k)) brs in
  (match match p' with
         | Coq_true -> closedu k c
         | Coq_false -> Coq_false with
   | Coq_true -> brs'
   | Coq_false -> Coq_false)
| Coq_tProj (_, c) -> closedu k c
| Coq_tFix (mfix, _) -> forallb (test_def (closedu k) (closedu k)) mfix
| Coq_tCoFix (mfix, _) -> forallb (test_def (closedu k) (closedu k)) mfix
| _ -> Coq_true

module TemplateTerm =
 struct
  type term = Coq__1.term

  (** val tRel : nat -> Coq__1.term **)

  let tRel x =
    Coq_tRel x

  (** val tSort : Universe.t -> Coq__1.term **)

  let tSort x =
    Coq_tSort x

  (** val tProd : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tProd x x0 x1 =
    Coq_tProd (x, x0, x1)

  (** val tLambda : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tLambda x x0 x1 =
    Coq_tLambda (x, x0, x1)

  (** val tLetIn :
      aname -> Coq__1.term -> Coq__1.term -> Coq__1.term -> Coq__1.term **)

  let tLetIn x x0 x1 x2 =
    Coq_tLetIn (x, x0, x1, x2)

  (** val tInd : inductive -> Instance.t -> Coq__1.term **)

  let tInd x x0 =
    Coq_tInd (x, x0)

  (** val tProj : projection -> Coq__1.term -> Coq__1.term **)

  let tProj x x0 =
    Coq_tProj (x, x0)

  (** val mkApps : Coq__1.term -> Coq__1.term list -> Coq__1.term **)

  let mkApps =
    mkApps

  (** val lift : nat -> nat -> Coq__1.term -> Coq__1.term **)

  let lift =
    lift

  (** val subst : Coq__1.term list -> nat -> Coq__1.term -> Coq__1.term **)

  let subst =
    subst

  (** val closedn : nat -> Coq__1.term -> bool **)

  let closedn =
    closedn

  (** val noccur_between : nat -> nat -> Coq__1.term -> bool **)

  let noccur_between =
    noccur_between

  (** val subst_instance_constr : Instance.t -> Coq__1.term -> Coq__1.term **)

  let subst_instance_constr =
    subst_instance subst_instance_constr
 end

module Env = Environment.Environment(TemplateTerm)

(** val destArity :
    term context_decl list -> term -> (term context_decl list, Universe.t)
    prod option **)

let rec destArity _UU0393_ = function
| Coq_tSort s -> Some (Coq_pair (_UU0393_, s))
| Coq_tProd (na, t1, b) -> destArity (snoc _UU0393_ (Env.vass na t1)) b
| Coq_tLetIn (na, b, b_ty, b') ->
  destArity (snoc _UU0393_ (Env.vdef na b b_ty)) b'
| _ -> None

(** val inds :
    kername -> Instance.t -> Env.one_inductive_body list -> term list **)

let inds ind u l =
  let rec aux = function
  | O -> Coq_nil
  | S n0 ->
    Coq_cons ((Coq_tInd ({ inductive_mind = ind; inductive_ind = n0 }, u)),
      (aux n0))
  in aux (length l)

module TemplateTermUtils =
 struct
  (** val destArity :
      term context_decl list -> term -> (term context_decl list, Universe.t)
      prod option **)

  let destArity =
    destArity

  (** val inds :
      kername -> Instance.t -> Env.one_inductive_body list -> term list **)

  let inds =
    inds
 end

module TemplateLookup = Lookup(TemplateTerm)(Env)

(** val lookup_constant_gen :
    (kername -> Env.global_decl option) -> kername -> Env.constant_body option **)

let lookup_constant_gen lookup kn =
  match lookup kn with
  | Some g ->
    (match g with
     | Env.ConstantDecl d -> Some d
     | Env.InductiveDecl _ -> None)
  | None -> None

(** val lookup_constant :
    Env.global_env -> kername -> Env.constant_body option **)

let lookup_constant _UU03a3_ =
  lookup_constant_gen (Env.lookup_env _UU03a3_)

(** val lookup_minductive_gen :
    (kername -> Env.global_decl option) -> kername ->
    Env.mutual_inductive_body option **)

let lookup_minductive_gen lookup mind =
  match lookup mind with
  | Some g ->
    (match g with
     | Env.ConstantDecl _ -> None
     | Env.InductiveDecl decl -> Some decl)
  | None -> None

(** val lookup_minductive :
    Env.global_env -> kername -> Env.mutual_inductive_body option **)

let lookup_minductive _UU03a3_ =
  lookup_minductive_gen (Env.lookup_env _UU03a3_)

(** val lookup_inductive_gen :
    (kername -> Env.global_decl option) -> inductive ->
    (Env.mutual_inductive_body, Env.one_inductive_body) prod option **)

let lookup_inductive_gen lookup ind =
  match lookup_minductive_gen lookup ind.inductive_mind with
  | Some mdecl ->
    (match nth_error (Env.ind_bodies mdecl) ind.inductive_ind with
     | Some idecl -> Some (Coq_pair (mdecl, idecl))
     | None -> None)
  | None -> None

(** val lookup_inductive :
    Env.global_env -> inductive -> (Env.mutual_inductive_body,
    Env.one_inductive_body) prod option **)

let lookup_inductive _UU03a3_ =
  lookup_inductive_gen (Env.lookup_env _UU03a3_)

(** val lookup_constructor_gen :
    (kername -> Env.global_decl option) -> inductive -> nat ->
    ((Env.mutual_inductive_body, Env.one_inductive_body) prod,
    Env.constructor_body) prod option **)

let lookup_constructor_gen lookup ind k =
  match lookup_inductive_gen lookup ind with
  | Some p ->
    let Coq_pair (mdecl, idecl) = p in
    (match nth_error (Env.ind_ctors idecl) k with
     | Some cdecl -> Some (Coq_pair ((Coq_pair (mdecl, idecl)), cdecl))
     | None -> None)
  | None -> None

(** val lookup_constructor :
    Env.global_env -> inductive -> nat -> ((Env.mutual_inductive_body,
    Env.one_inductive_body) prod, Env.constructor_body) prod option **)

let lookup_constructor _UU03a3_ =
  lookup_constructor_gen (Env.lookup_env _UU03a3_)

(** val lookup_projection_gen :
    (kername -> Env.global_decl option) -> projection ->
    (((Env.mutual_inductive_body, Env.one_inductive_body) prod,
    Env.constructor_body) prod, Env.projection_body) prod option **)

let lookup_projection_gen lookup p =
  match lookup_constructor_gen lookup p.proj_ind O with
  | Some p0 ->
    let Coq_pair (p1, cdecl) = p0 in
    let Coq_pair (mdecl, idecl) = p1 in
    (match nth_error (Env.ind_projs idecl) p.proj_arg with
     | Some pdecl ->
       Some (Coq_pair ((Coq_pair ((Coq_pair (mdecl, idecl)), cdecl)), pdecl))
     | None -> None)
  | None -> None

(** val lookup_projection :
    Env.global_env -> projection -> (((Env.mutual_inductive_body,
    Env.one_inductive_body) prod, Env.constructor_body) prod,
    Env.projection_body) prod option **)

let lookup_projection _UU03a3_ =
  lookup_projection_gen (Env.lookup_env _UU03a3_)

(** val on_udecl_decl : (universes_decl -> 'a1) -> Env.global_decl -> 'a1 **)

let on_udecl_decl f = function
| Env.ConstantDecl cb -> f (Env.cst_universes cb)
| Env.InductiveDecl mb -> f (Env.ind_universes mb)

(** val universes_decl_of_decl : Env.global_decl -> universes_decl **)

let universes_decl_of_decl =
  on_udecl_decl (fun x -> x)

(** val global_levels : ContextSet.t -> LevelSet.t **)

let global_levels univs =
  LevelSet.union (ContextSet.levels univs)
    (LevelSet.singleton Level.Coq_lzero)

(** val global_constraints : Env.global_env -> ConstraintSet.t **)

let global_constraints _UU03a3_ =
  snd (Env.universes _UU03a3_)

(** val global_uctx : Env.global_env -> ContextSet.t **)

let global_uctx _UU03a3_ =
  Coq_pair ((global_levels (Env.universes _UU03a3_)),
    (global_constraints _UU03a3_))

(** val global_ext_levels : Env.global_env_ext -> LevelSet.t **)

let global_ext_levels _UU03a3_ =
  LevelSet.union (levels_of_udecl (snd _UU03a3_))
    (global_levels (Env.universes (fst _UU03a3_)))

(** val global_ext_constraints : Env.global_env_ext -> ConstraintSet.t **)

let global_ext_constraints _UU03a3_ =
  ConstraintSet.union (constraints_of_udecl (snd _UU03a3_))
    (global_constraints (fst _UU03a3_))

(** val global_ext_uctx : Env.global_env_ext -> ContextSet.t **)

let global_ext_uctx _UU03a3_ =
  Coq_pair ((global_ext_levels _UU03a3_), (global_ext_constraints _UU03a3_))

(** val wf_universe_dec : Env.global_env_ext -> Universe.t -> sumbool **)

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
    checker_flags -> Env.global_env -> inductive -> Env.mutual_inductive_body
    -> Env.one_inductive_body -> (Env.constructor_body, __) coq_Alli **)

let declared_ind_declared_constructors =
  TemplateLookup.declared_ind_declared_constructors

(** val tDummy : term **)

let tDummy =
  Coq_tVar String.EmptyString

(** val mkApp : term -> term -> term **)

let mkApp t0 u =
  match t0 with
  | Coq_tApp (f, args) -> Coq_tApp (f, (app args (Coq_cons (u, Coq_nil))))
  | _ -> Coq_tApp (t0, (Coq_cons (u, Coq_nil)))

(** val isApp : term -> bool **)

let isApp = function
| Coq_tApp (_, _) -> Coq_true
| _ -> Coq_false

(** val isLambda : term -> bool **)

let isLambda = function
| Coq_tLambda (_, _, _) -> Coq_true
| _ -> Coq_false

type parameter_entry = { parameter_entry_type : term;
                         parameter_entry_universes : universes_entry }

(** val parameter_entry_type : parameter_entry -> term **)

let parameter_entry_type p =
  p.parameter_entry_type

(** val parameter_entry_universes : parameter_entry -> universes_entry **)

let parameter_entry_universes p =
  p.parameter_entry_universes

type definition_entry = { definition_entry_type : term option;
                          definition_entry_body : term;
                          definition_entry_universes : universes_entry;
                          definition_entry_opaque : bool }

(** val definition_entry_type : definition_entry -> term option **)

let definition_entry_type d =
  d.definition_entry_type

(** val definition_entry_body : definition_entry -> term **)

let definition_entry_body d =
  d.definition_entry_body

(** val definition_entry_universes : definition_entry -> universes_entry **)

let definition_entry_universes d =
  d.definition_entry_universes

(** val definition_entry_opaque : definition_entry -> bool **)

let definition_entry_opaque d =
  d.definition_entry_opaque

type constant_entry =
| ParameterEntry of parameter_entry
| DefinitionEntry of definition_entry

(** val constant_entry_rect :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1 **)

let constant_entry_rect f f0 = function
| ParameterEntry p -> f p
| DefinitionEntry def -> f0 def

(** val constant_entry_rec :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1 **)

let constant_entry_rec f f0 = function
| ParameterEntry p -> f p
| DefinitionEntry def -> f0 def

type one_inductive_entry = { mind_entry_typename : ident;
                             mind_entry_arity : term;
                             mind_entry_consnames : ident list;
                             mind_entry_lc : term list }

(** val mind_entry_typename : one_inductive_entry -> ident **)

let mind_entry_typename o =
  o.mind_entry_typename

(** val mind_entry_arity : one_inductive_entry -> term **)

let mind_entry_arity o =
  o.mind_entry_arity

(** val mind_entry_consnames : one_inductive_entry -> ident list **)

let mind_entry_consnames o =
  o.mind_entry_consnames

(** val mind_entry_lc : one_inductive_entry -> term list **)

let mind_entry_lc o =
  o.mind_entry_lc

type mutual_inductive_entry = { mind_entry_record : ident option option;
                                mind_entry_finite : recursivity_kind;
                                mind_entry_params : Env.context;
                                mind_entry_inds : one_inductive_entry list;
                                mind_entry_universes : universes_entry;
                                mind_entry_template : bool;
                                mind_entry_variance : Variance.t option list
                                                      option;
                                mind_entry_private : bool option }

(** val mind_entry_record : mutual_inductive_entry -> ident option option **)

let mind_entry_record m =
  m.mind_entry_record

(** val mind_entry_finite : mutual_inductive_entry -> recursivity_kind **)

let mind_entry_finite m =
  m.mind_entry_finite

(** val mind_entry_params : mutual_inductive_entry -> Env.context **)

let mind_entry_params m =
  m.mind_entry_params

(** val mind_entry_inds :
    mutual_inductive_entry -> one_inductive_entry list **)

let mind_entry_inds m =
  m.mind_entry_inds

(** val mind_entry_universes : mutual_inductive_entry -> universes_entry **)

let mind_entry_universes m =
  m.mind_entry_universes

(** val mind_entry_template : mutual_inductive_entry -> bool **)

let mind_entry_template m =
  m.mind_entry_template

(** val mind_entry_variance :
    mutual_inductive_entry -> Variance.t option list option **)

let mind_entry_variance m =
  m.mind_entry_variance

(** val mind_entry_private : mutual_inductive_entry -> bool option **)

let mind_entry_private m =
  m.mind_entry_private

(** val ind_predicate_context :
    inductive -> Env.mutual_inductive_body -> Env.one_inductive_body ->
    Env.context **)

let ind_predicate_context ind mdecl idecl =
  let ictx =
    Env.expand_lets_ctx (Env.ind_params mdecl) (Env.ind_indices idecl)
  in
  let indty =
    mkApps (Coq_tInd (ind, (abstract_instance (Env.ind_universes mdecl))))
      (Env.to_extended_list
        (Env.app_context (Env.smash_context Coq_nil (Env.ind_params mdecl))
          ictx))
  in
  let inddecl = { decl_name = { binder_name = (Coq_nNamed
    (Env.ind_name idecl)); binder_relevance = (Env.ind_relevance idecl) };
    decl_body = None; decl_type = indty }
  in
  Coq_cons (inddecl, ictx)

(** val inst_case_context :
    term list -> Instance.t -> Env.context -> Env.context **)

let inst_case_context params puinst0 pctx =
  Env.subst_context (List.rev params) O
    (subst_instance Env.subst_instance_context puinst0 pctx)

(** val pre_case_predicate_context_gen :
    inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
    list -> Instance.t -> Env.context **)

let pre_case_predicate_context_gen ind mdecl idecl params puinst0 =
  inst_case_context params puinst0 (ind_predicate_context ind mdecl idecl)

(** val case_predicate_context_gen :
    inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
    list -> Instance.t -> aname list -> term context_decl list **)

let case_predicate_context_gen ind mdecl idecl params puinst0 pctx =
  map2 Env.set_binder_name pctx
    (pre_case_predicate_context_gen ind mdecl idecl params puinst0)

(** val case_predicate_context :
    inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
    predicate -> Env.context **)

let case_predicate_context ind mdecl idecl p =
  case_predicate_context_gen ind mdecl idecl p.pparams p.puinst p.pcontext

(** val cstr_branch_context :
    inductive -> Env.mutual_inductive_body -> Env.constructor_body ->
    Env.context **)

let cstr_branch_context ind mdecl cdecl =
  Env.expand_lets_ctx (Env.ind_params mdecl)
    (Env.subst_context
      (inds ind.inductive_mind (abstract_instance (Env.ind_universes mdecl))
        (Env.ind_bodies mdecl)) (length (Env.ind_params mdecl))
      (Env.cstr_args cdecl))

(** val case_branch_context_gen :
    inductive -> Env.mutual_inductive_body -> term list -> Instance.t ->
    aname list -> Env.constructor_body -> Env.context **)

let case_branch_context_gen ind mdecl params puinst0 bctx cdecl =
  map2 Env.set_binder_name bctx
    (inst_case_context params puinst0 (cstr_branch_context ind mdecl cdecl))

(** val case_branch_context :
    inductive -> Env.mutual_inductive_body -> Env.constructor_body -> term
    predicate -> term branch -> Env.context **)

let case_branch_context ind mdecl cdecl p br =
  case_branch_context_gen ind mdecl p.pparams p.puinst br.bcontext cdecl

(** val case_branches_contexts_gen :
    inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
    list -> Instance.t -> term branch list -> Env.context list **)

let case_branches_contexts_gen ind mdecl idecl params puinst0 brs =
  map2 (fun br cdecl ->
    case_branch_context_gen ind mdecl params puinst0 br.bcontext cdecl) brs
    (Env.ind_ctors idecl)

(** val case_branches_contexts :
    inductive -> Env.mutual_inductive_body -> Env.one_inductive_body -> term
    predicate -> term branch list -> Env.context list **)

let case_branches_contexts ind mdecl idecl p brs =
  map2 (fun br ->
    case_branch_context_gen ind mdecl p.pparams p.puinst br.bcontext) brs
    (Env.ind_ctors idecl)

(** val case_branch_type_gen :
    inductive -> Env.mutual_inductive_body -> term list -> Instance.t -> term
    -> nat -> Env.constructor_body -> term branch -> (Env.context, term) prod **)

let case_branch_type_gen ind mdecl params puinst0 ptm i cdecl br =
  let cstr = Coq_tConstruct (ind, i, puinst0) in
  let args = Env.to_extended_list (Env.cstr_args cdecl) in
  let cstrapp =
    mkApps cstr
      (app (map (lift (length (Env.cstr_args cdecl)) O) params) args)
  in
  let brctx =
    case_branch_context_gen ind mdecl params puinst0 br.bcontext cdecl
  in
  let upars =
    subst_instance Env.subst_instance_context puinst0 (Env.ind_params mdecl)
  in
  let indices =
    map (subst (List.rev params) (length (Env.cstr_args cdecl)))
      (map (Env.expand_lets_k upars (length (Env.cstr_args cdecl)))
        (map
          (subst (inds ind.inductive_mind puinst0 (Env.ind_bodies mdecl))
            (Nat.add (length (Env.ind_params mdecl))
              (length (Env.cstr_args cdecl))))
          (map (subst_instance subst_instance_constr puinst0)
            (Env.cstr_indices cdecl))))
  in
  let ty =
    mkApps (lift (length (Env.cstr_args cdecl)) O ptm)
      (app indices (Coq_cons (cstrapp, Coq_nil)))
  in
  Coq_pair (brctx, ty)

(** val case_branch_type :
    inductive -> Env.mutual_inductive_body -> term predicate -> term -> nat
    -> Env.constructor_body -> term branch -> (Env.context, term) prod **)

let case_branch_type ind mdecl p ptm i cdecl br =
  case_branch_type_gen ind mdecl p.pparams p.puinst ptm i cdecl br
