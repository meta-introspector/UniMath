open Notations
open PartA
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open UnivalenceAxiom

(** val subtype_set : hSet **)

let subtype_set =
  make_hSet isasethsubtype

(** val subtype_isIn :
    'a1 hsubtype -> 'a1 carrier -> 'a1 hsubtype -> hProp **)

let subtype_isIn _ s t =
  t s.pr1

(** val subtype_containedIn : pr1hSet hrel **)

let subtype_containedIn _ t =
  forall_hProp (fun x -> himpl (Obj.magic t x))

(** val subtype_notContainedIn : 'a1 hsubtype -> 'a1 hsubtype -> hProp **)

let subtype_notContainedIn _ _ =
  ishinh

(** val subtype_inc :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> 'a1 carrier -> 'a1 carrier **)

let subtype_inc _ _ le s =
  { pr1 = s.pr1; pr2 = (Obj.magic le s.pr1 s.pr2) }

(** val subtype_equal : 'a1 hsubtype -> 'a1 hsubtype -> hProp **)

let subtype_equal s t =
  forall_hProp (fun x -> hequiv (s x) (t x))

(** val subtype_notEqual : 'a1 hsubtype -> 'a1 hsubtype -> hProp **)

let subtype_notEqual _ _ =
  hdisj

(** val subtype_notEqual_containedIn :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType **)

let subtype_notEqual_containedIn s t ci ne =
  squash_to_hProp (subtype_notContainedIn t s) ne (fun x0 ->
    match x0 with
    | Coq_ii1 h ->
      squash_to_hProp (subtype_notContainedIn t s) h (fun x1 ->
        let x = x1.pr1 in
        let pr3 = x1.pr2 in
        let p = pr3.pr1 in let q = pr3.pr2 in fromempty (q (Obj.magic ci x p)))
    | Coq_ii2 h -> h)

(** val subtype_notEqual_from_negEqual :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType **)

let subtype_notEqual_from_negEqual s t lem ne =
  let q = negforall_to_existsneg (fun x -> hequiv (s x) (t x)) lem ne in
  squash_to_hProp (subtype_notEqual s t) q (fun x0 ->
    let x = x0.pr1 in
    let n = x0.pr2 in
    let r = weak_fromnegdirprod (himpl (t x)) (himpl (s x)) n in
    let s0 = proof_by_contradiction hdisj lem (Obj.magic r) in
    squash_to_hProp hdisj s0 (fun s1 ->
      hinhpr
        (match s1 with
         | Coq_ii1 a ->
           Coq_ii1
             (hinhpr { pr1 = x; pr2 = (negimpl_to_conj (s x) (t x) lem a) })
         | Coq_ii2 b ->
           Coq_ii2
             (hinhpr { pr1 = x; pr2 = (negimpl_to_conj (t x) (s x) lem b) }))))

(** val subtype_equal_cond : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType **)

let subtype_equal_cond _ _ =
  Obj.magic { pr1 = (fun c x ->
    let st = c.pr1 in
    let ts = c.pr2 in { pr1 = (fun s -> st x s); pr2 = (fun t -> ts x t) });
    pr2 = (fun e -> { pr1 = (fun x s -> (e x).pr1 s); pr2 = (fun x t ->
    (e x).pr2 t) }) }

(** val subtype_union : ('a2 -> 'a1 hsubtype) -> 'a1 hsubtype **)

let subtype_union _ _ =
  ishinh

(** val subtype_union_containedIn :
    hSet -> ('a1 -> pr1hSet hsubtype) -> 'a1 -> hProptoType **)

let subtype_union_containedIn _ _ i =
  Obj.magic (fun _ s -> hinhpr { pr1 = i; pr2 = s })

(** val hsubtype_univalence :
    'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths, hProptoType) weq **)

let hsubtype_univalence s t =
  weqcomp (Obj.magic weqtoforallpaths s t)
    (Obj.magic weqonsecfibers (fun x -> weqlogeq (s x) (t x)))

(** val subtype_containment_istrans : pr1hSet istrans **)

let subtype_containment_istrans _ _ _ i j =
  Obj.magic (fun x -> funcomp (Obj.magic i x) (Obj.magic j x))

(** val subtype_containment_isrefl : pr1hSet isrefl **)

let subtype_containment_isrefl _ =
  Obj.magic (fun _ s -> s)

(** val subtype_containment_ispreorder : pr1hSet ispreorder **)

let subtype_containment_ispreorder =
  make_dirprod subtype_containment_istrans subtype_containment_isrefl

(** val subtype_containment_isantisymm : pr1hSet isantisymm **)

let subtype_containment_isantisymm s t i j =
  invmap (Obj.magic hsubtype_univalence s t)
    (let x0 = fun s0 t0 -> (Obj.magic subtype_equal_cond s0 t0).pr1 in
     Obj.magic x0 s t { pr1 = i; pr2 = j })

(** val subtype_containment_isPartialOrder : pr1hSet isPartialOrder **)

let subtype_containment_isPartialOrder =
  make_dirprod subtype_containment_ispreorder subtype_containment_isantisymm

(** val subtype_plus : 'a1 hsubtype -> 'a1 -> 'a1 hsubtype **)

let subtype_plus _ _ _ =
  hdisj

(** val subtype_plus_incl : 'a1 hsubtype -> 'a1 -> hProptoType **)

let subtype_plus_incl _ _ =
  Obj.magic (fun _ ss -> hinhpr (Coq_ii1 ss))

(** val subtype_plus_has_point : 'a1 hsubtype -> 'a1 -> hProptoType **)

let subtype_plus_has_point _ _ =
  hinhpr (Coq_ii2 Coq_paths_refl)

(** val subtype_plus_in :
    'a1 hsubtype -> 'a1 -> 'a1 hsubtype -> hProptoType -> hProptoType ->
    hProptoType **)

let subtype_plus_in _ _ t le tz =
  Obj.magic (fun x s'x ->
    squash_to_hProp (t x) s'x (fun x0 ->
      match x0 with
      | Coq_ii1 h -> Obj.magic le x h
      | Coq_ii2 _ -> tz))
