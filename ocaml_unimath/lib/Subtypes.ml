open Notations
open PartA
open PartB
open PartC
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

(** val subtype_smallerThan : 'a1 hsubtype -> 'a1 hsubtype -> hProp **)

let subtype_smallerThan s t =
  hconj (subtype_containedIn (Obj.magic s) (Obj.magic t))
    (subtype_notContainedIn t s)

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

(** val subtype_notEqual_to_negEqual :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType **)

let subtype_notEqual_to_negEqual _ _ n =
  squash_to_prop n isapropneg (fun x0 ->
    match x0 with
    | Coq_ii1 h ->
      squash_to_prop h isapropneg (fun x1 ->
        let x = x1.pr1 in
        let pr3 = x1.pr2 in
        let sx = pr3.pr1 in
        let nTx = pr3.pr2 in Obj.magic (fun e -> nTx ((e x).pr1 sx)))
    | Coq_ii2 h ->
      squash_to_prop h isapropneg (fun x1 ->
        let x = x1.pr1 in
        let pr3 = x1.pr2 in
        let tx = pr3.pr1 in
        let nSx = pr3.pr2 in Obj.magic (fun e -> nSx ((e x).pr2 tx))))

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

(** val emptysubtype : 'a1 hsubtype **)

let emptysubtype _ =
  hfalse

(** val subtype_difference : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype **)

let subtype_difference s _ x =
  hconj (s x) hneg

(** val subtype_difference_containedIn :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType **)

let subtype_difference_containedIn _ _ =
  Obj.magic (fun _ u -> u.pr1)

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

(** val subtype_binaryunion : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype **)

let subtype_binaryunion _ _ _ =
  hdisj

(** val subtype_binaryunion_leq1 :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType **)

let subtype_binaryunion_leq1 _ _ =
  Obj.magic (fun _ -> hdisj_in1)

(** val subtype_binaryunion_leq2 :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType **)

let subtype_binaryunion_leq2 _ _ =
  Obj.magic (fun _ -> hdisj_in2)

(** val subtype_union_containedIn :
    hSet -> ('a1 -> pr1hSet hsubtype) -> 'a1 -> hProptoType **)

let subtype_union_containedIn _ _ i =
  Obj.magic (fun _ s -> hinhpr { pr1 = i; pr2 = s })

(** val subtype_intersection : ('a2 -> 'a1 hsubtype) -> 'a1 hsubtype **)

let subtype_intersection s x =
  forall_hProp (fun i -> s i x)

(** val hsubtype_univalence :
    'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths, hProptoType) weq **)


(** val hsubtype_rect :
    'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths -> 'a2, hProptoType
    -> 'a2) weq **)


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


(** val subtype_containment_isPartialOrder : pr1hSet isPartialOrder **)


(** val subtype_inc_comp :
    'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> hProptoType ->
    hProptoType -> 'a1 carrier -> 'a1 carrier paths **)

let subtype_inc_comp _ _ _ _ _ _ =
  Coq_paths_refl

(** val subtype_deceq : 'a1 hsubtype -> 'a1 isdeceq -> 'a1 carrier isdeceq **)

let subtype_deceq s i s0 t =
  let d = i s0.pr1 t.pr1 in
  (match d with
   | Coq_ii1 a -> Coq_ii1 (subtypePath_prop s s0 t a)
   | Coq_ii2 b ->
     Coq_ii2 (fun eq -> b (maponpaths (fun t0 -> t0.pr1) s0 t eq)))

type 'x isDecidablePredicate = 'x -> hProptoType decidable

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

(** val subtype_complement : 'a1 hsubtype -> 'a1 hsubtype **)

let subtype_complement _ _ =
  hneg

(** val not_in_subtype_and_complement :
    'a1 hsubtype -> 'a1 -> hProptoType -> hProptoType -> empty **)

let not_in_subtype_and_complement _ _ in_S in_neg_S =
  Obj.magic in_neg_S in_S

(** val subtype_complement_intersection_empty :
    'a1 hsubtype -> ('a2 -> 'a1 hsubtype) -> ('a2, 'a1 hsubtype paths) total2
    -> ('a2, 'a1 hsubtype paths) total2 -> hProptoType **)

let subtype_complement_intersection_empty s f x x0 =
  let subtype_complement_intersection_empty_subproof =
    fun _ _ has_S _ in_intersection -> in_intersection has_S.pr1
  in
  let subtype_complement_intersection_empty_subproof0 =
    fun _ _ has_neg_S _ in_intersection -> in_intersection has_neg_S.pr1
  in
  Obj.magic (fun x1 ->
    make_dirprod (fun in_intersection ->
      not_in_subtype_and_complement s x1
        (subtype_complement_intersection_empty_subproof s f x x1
          in_intersection)
        (subtype_complement_intersection_empty_subproof0 s f x0 x1
          in_intersection)) (fun _ -> assert false (* absurd case *)))

(** val subtype_complement_union :
    'a1 hsubtype -> hProptoType -> ('a2 -> 'a1 hsubtype) -> ('a2, 'a1
    hsubtype paths) total2 -> ('a2, 'a1 hsubtype paths) total2 -> hProptoType **)

let subtype_complement_union s lem f x x0 =
  let subtype_complement_union_subproof = fun s0 f0 has_S _ a ->
    internal_paths_rew_r (f0 has_S.pr1) s0 a has_S.pr2
  in
  let subtype_complement_union_subproof0 = fun s0 f0 has_neg_S _ b ->
    internal_paths_rew_r (f0 has_neg_S.pr1) (subtype_complement s0) b
      has_neg_S.pr2
  in
  Obj.magic (fun x1 ->
    make_dirprod (fun _ -> Coq_tt) (fun _ ->
      let h = Obj.magic lem (s x1) in
      (match h with
       | Coq_ii1 a ->
         hinhpr { pr1 = x.pr1; pr2 =
           (subtype_complement_union_subproof s f x x1 a) }
       | Coq_ii2 b ->
         hinhpr { pr1 = x0.pr1; pr2 =
           (subtype_complement_union_subproof0 s f x0 x1 b) })))

(** val binary_intersection' :
    'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype **)

let binary_intersection' u v =
  subtype_intersection (fun b -> match b with
                                 | Coq_true -> u
                                 | Coq_false -> v)

(** val binary_intersection : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype **)

let binary_intersection u v x =
  hconj (u x) (v x)

(** val binary_intersection_commutative :
    'a1 hsubtype -> 'a1 hsubtype -> 'a1 -> hProptoType -> hProptoType **)

let binary_intersection_commutative u v x p =
  transportf (hconj (u x) (v x)) (hconj (v x) (u x))
    (iscomm_hconj (u x) (v x)) p

(** val intersection_contained_l :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType **)

let intersection_contained_l _ _ =
  Obj.magic (fun _ xinUV -> xinUV.pr1)

(** val intersection_contained_r :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType **)

let intersection_contained_r _ _ =
  Obj.magic (fun _ xinUV -> xinUV.pr2)

(** val intersection_contained :
    'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype ->
    hProptoType -> hProptoType -> hProptoType **)

let intersection_contained u _ v _ uu vv =
  Obj.magic (fun x p -> { pr1 =
    (Obj.magic uu x (Obj.magic intersection_contained_l u v x p)); pr2 =
    (Obj.magic vv x (Obj.magic intersection_contained_r u v x p)) })

(** val isaprop_subtype_containedIn :
    'a1 hsubtype -> 'a1 hsubtype -> hProptoType isaprop **)

let isaprop_subtype_containedIn _ v =
  impred_isaprop (fun t -> isapropimpl (v t).pr2)

(** val image_hsubtype : 'a1 hsubtype -> ('a1 -> 'a2) -> 'a2 hsubtype **)

let image_hsubtype _ _ _ =
  ishinh

(** val image_hsubtype_emptyhsubtype : ('a1 -> 'a2) -> 'a2 hsubtype paths **)


(** val image_hsubtype_id : 'a1 hsubtype -> 'a1 hsubtype paths **)


(** val image_hsubtype_comp :
    'a1 hsubtype -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 hsubtype paths **)


type ('x, 'y) hsubtype_preserving = hProptoType

(** val isaprop_hsubtype_preserving :
    'a1 hsubtype -> 'a2 hsubtype -> ('a1 -> 'a2) -> ('a1, 'a2)
    hsubtype_preserving isaprop **)

let isaprop_hsubtype_preserving _ v _ =
  impred_isaprop (fun t -> isapropimpl (v t).pr2)

(** val id_hsubtype_preserving :
    'a1 hsubtype -> ('a1, 'a1) hsubtype_preserving **)

let id_hsubtype_preserving u =
  Obj.magic (fun _ xinU ->
    internal_paths_rew (image_hsubtype u idfun) xinU u (image_hsubtype_id u))

(** val comp_hsubtype_preserving :
    'a1 hsubtype -> 'a2 hsubtype -> 'a3 hsubtype -> ('a1 -> 'a2) -> ('a2 ->
    'a3) -> ('a1, 'a2) hsubtype_preserving -> ('a2, 'a3) hsubtype_preserving
    -> ('a1, 'a3) hsubtype_preserving **)

let comp_hsubtype_preserving u _ _ f g fsp gsp =
  Obj.magic (fun z zinU ->
    let zinU0 =
      internal_paths_rew (image_hsubtype u (funcomp f g)) zinU
        (image_hsubtype (image_hsubtype u f) g) (image_hsubtype_comp u f g)
    in
    Obj.magic gsp z
      (factor_through_squash ishinh.pr2 (fun y ->
        hinhpr { pr1 = y.pr1; pr2 = { pr1 = y.pr2.pr1; pr2 =
          (Obj.magic fsp y.pr1 y.pr2.pr2) } }) zinU0))

(** val empty_hsubtype_preserving :
    ('a1 -> 'a2) -> ('a1, 'a2) hsubtype_preserving **)

let empty_hsubtype_preserving f =
  internal_paths_rew_r (image_hsubtype emptysubtype f) emptysubtype
    (subtype_containment_isrefl (Obj.magic emptysubtype))
    (image_hsubtype_emptyhsubtype f)

(** val total_hsubtype_preserving :
    ('a1 -> 'a2) -> ('a1, 'a2) hsubtype_preserving **)

let total_hsubtype_preserving _ =
  Obj.magic (fun _ _ -> Coq_tt)

(** val singleton : 'a1 -> 'a1 hsubtype **)

let singleton _ _ =
  ishinh

(** val singleton_point : 'a1 -> 'a1 carrier **)

let singleton_point x =
  { pr1 = x; pr2 = (hinhpr Coq_paths_refl) }

(** val iscontr_singleton : hSet -> pr1hSet -> pr1hSet carrier iscontr **)

let iscontr_singleton x x0 =
  make_iscontr (singleton_point x0) (fun t ->
    subtypePath_prop (singleton x0) t (singleton_point x0)
      (squash_to_prop t.pr2 (setproperty x t.pr1 (singleton_point x0).pr1)
        (fun x1 -> x1)))

(** val singleton_is_in : 'a1 hsubtype -> 'a1 carrier -> hProptoType **)

let singleton_is_in a a0 =
  Obj.magic (fun y -> hinhuniv (a y) (fun p -> transportb y a0.pr1 p a0.pr2))

(** val coprod_carrier_binary_union :
    'a1 hsubtype -> 'a1 hsubtype -> ('a1 carrier, 'a1 carrier) coprod -> 'a1
    carrier **)

let coprod_carrier_binary_union a b =
  sumofmaps
    (subtype_inc a (subtype_binaryunion a b) (subtype_binaryunion_leq1 a b))
    (subtype_inc b (subtype_binaryunion a b) (subtype_binaryunion_leq2 a b))

(** val issurjective_coprod_carrier_binary_union :
    'a1 hsubtype -> 'a1 hsubtype -> (('a1 carrier, 'a1 carrier) coprod, 'a1
    carrier) issurjective **)

let issurjective_coprod_carrier_binary_union a b y =
  let x = y.pr1 in
  let aub = y.pr2 in
  hinhfun
    (sumofmaps (fun y0 ->
      make_hfiber (coprod_carrier_binary_union a b) { pr1 = x; pr2 = aub }
        (Coq_ii1 { pr1 = x; pr2 = y0 })
        (subtypePath_prop (subtype_binaryunion a b)
          (coprod_carrier_binary_union a b (Coq_ii1 { pr1 = x; pr2 = y0 }))
          { pr1 = x; pr2 = aub } Coq_paths_refl)) (fun y0 ->
      make_hfiber (coprod_carrier_binary_union a b) { pr1 = x; pr2 = aub }
        (Coq_ii2 { pr1 = x; pr2 = y0 })
        (subtypePath_prop (subtype_binaryunion a b)
          (coprod_carrier_binary_union a b (Coq_ii2 { pr1 = x; pr2 = y0 }))
          { pr1 = x; pr2 = aub } Coq_paths_refl))) aub
