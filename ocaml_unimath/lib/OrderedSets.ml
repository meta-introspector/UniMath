open DecidablePropositions
open FiniteSets
open NaturalNumbers
open PartA
open PartB
open PartD
open Preamble
open Propositions
open Sets
open StandardFiniteSets
open UnivalenceAxiom

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val isTotalOrder : hSet -> pr1hSet hrel -> hProp **)

let isTotalOrder x r =
  make_hProp
    (isapropdirprod (isaprop_isPartialOrder x r) (isaprop_istotal x r))

(** val tot_nge_to_le :
    hSet -> pr1hSet hrel -> pr1hSet istotal -> pr1hSet -> pr1hSet ->
    hProptoType -> hProptoType **)

let tot_nge_to_le _ r tot x y nle =
  hdisjtoimpl (r y x) (tot x y) nle

(** val tot_nle_iff_gt :
    hSet -> pr1hSet hrel -> hProptoType -> pr1hSet -> pr1hSet ->
    (hProptoType, hProptoType) logeq **)

let tot_nle_iff_gt x r i =
  let tot = (Obj.magic i).pr2 in
  let refl = (Obj.magic i).pr1.pr1.pr2 in
  let anti = (Obj.magic i).pr1.pr2 in
  (fun x0 y -> { pr1 = (fun nle ->
  Obj.magic { pr1 = (tot_nge_to_le x r tot x0 y nle); pr2 = (fun _ ->
    Obj.magic nle (refl y)) }); pr2 = (fun yltx ->
  Obj.magic (fun xley ->
    let ylex = (Obj.magic yltx).pr1 in
    (Obj.magic yltx).pr2 (anti y x0 ylex xley))) })

type isSmallest = pr1hSet -> hProptoType

type isBiggest = pr1hSet -> hProptoType

type isMinimal = pr1hSet -> hProptoType -> pr1hSet paths

type isMaximal = pr1hSet -> hProptoType -> pr1hSet paths

type consecutive =
  ((hProptoType, pr1hSet paths neg) dirprod, pr1hSet -> hProptoType) dirprod

(** val isaprop_isSmallest : coq_Poset -> pr1hSet -> isSmallest isaprop **)

let isaprop_isSmallest x x0 =
  impred_prop (posetRelation x x0)

(** val isaprop_isBiggest : coq_Poset -> pr1hSet -> isBiggest isaprop **)

let isaprop_isBiggest x x0 =
  impred_prop (fun t -> posetRelation x t x0)

(** val coq_Poset_univalence_map :
    coq_Poset -> coq_Poset -> coq_Poset paths -> coq_PosetEquivalence **)

let coq_Poset_univalence_map x _ _ =
  identityPosetEquivalence x

(** val posetStructureIdentity :
    hSet -> coq_PartialOrder -> coq_PartialOrder -> (isPosetEquivalence,
    coq_PartialOrder paths) logeq **)


(** val posetTransport_weq :
    coq_Poset -> coq_Poset -> ((hSet, coq_PartialOrder) coq_PathPair,
    coq_PosetEquivalence) weq **)

let posetTransport_weq x y =
  weqbandf (hSet_univalence (carrierofposet x) (carrierofposet y)) (fun _ ->
    invweq
      (let x0 = x.pr1 in
       let r = x.pr2 in
       let s = y.pr2 in
       weqimplimpl (posetStructureIdentity x0 r s).pr1
         (posetStructureIdentity x0 r s).pr2
         (isaprop_isPosetEquivalence { pr1 = x0; pr2 = r } { pr1 = x0; pr2 =
           s } (hSet_univalence_map x0 x0 Coq_paths_refl))
         (isaset_PartialOrder x0 (transportf x0 x0 Coq_paths_refl r) s)))

(** val coq_Poset_univalence_0 :
    coq_Poset -> coq_Poset -> (coq_Poset paths, coq_PosetEquivalence) weq **)

let coq_Poset_univalence_0 x y =
  weqcomp (total2_paths_equiv x y) (posetTransport_weq x y)

(** val coq_Poset_univalence :
    coq_Poset -> coq_Poset -> (coq_Poset paths, coq_PosetEquivalence) weq **)

let coq_Poset_univalence x y =
  let k = fun e ->
    let x0 = fun x0 y0 x1 x' y1 ->
      (isinj_pr1_PosetEquivalence x0 y0 x1 x' y1).pr1
    in
    let x1 = pr1weq (coq_Poset_univalence_0 x y) e in
    let x' = coq_Poset_univalence_map x y e in
    let y0 = Coq_paths_refl in (x0 x y x1 x' y0).pr1
  in
  remakeweq (coq_Poset_univalence_0 x y) (coq_Poset_univalence_map x y) k

(** val coq_Poset_univalence_compute :
    coq_Poset -> coq_Poset -> coq_Poset paths -> coq_PosetEquivalence paths **)

let coq_Poset_univalence_compute _ _ _ =
  Coq_paths_refl

(** val coq_PosetEquivalence_rect :
    coq_Poset -> coq_Poset -> (coq_Poset paths -> 'a1) ->
    coq_PosetEquivalence -> 'a1 **)

let coq_PosetEquivalence_rect x y ih f =
  let p = ih (invmap (coq_Poset_univalence x y) f) in
  let h = homotweqinvweq (coq_Poset_univalence x y) f in
  transportf
    (pr1weq (coq_Poset_univalence x y) (invmap (coq_Poset_univalence x y) f))
    f h p

(** val isMinimal_preserved :
    coq_Poset -> coq_Poset -> pr1hSet -> isMinimal -> coq_PosetEquivalence ->
    isMinimal **)

let isMinimal_preserved x y _ is f =
  coq_PosetEquivalence_rect x y (fun _ -> is) f

(** val isMaximal_preserved :
    coq_Poset -> coq_Poset -> pr1hSet -> isMaximal -> coq_PosetEquivalence ->
    isMaximal **)

let isMaximal_preserved x y _ is f =
  coq_PosetEquivalence_rect x y (fun _ -> is) f

(** val consecutive_preserved :
    coq_Poset -> coq_Poset -> pr1hSet -> pr1hSet -> consecutive ->
    coq_PosetEquivalence -> consecutive **)

let consecutive_preserved x y _ _ is f =
  coq_PosetEquivalence_rect x y (fun _ -> is) f

type coq_OrderedSet = (coq_Poset, pr1hSet istotal) total2

(** val underlyingPoset : coq_OrderedSet -> coq_Poset **)

let underlyingPoset x =
  x.pr1

(** val coq_Poset_lessthan : coq_Poset -> pr1hSet -> pr1hSet -> hProp **)

let coq_Poset_lessthan _ _ _ =
  ishinh

(** val coq_OrderedSet_isrefl : coq_OrderedSet -> pr1hSet -> hProptoType **)

let coq_OrderedSet_isrefl x x0 =
  let x1 = x.pr1 in
  let _po_ = x1.pr2 in
  let _i_ = _po_.pr2 in let transrefl = _i_.pr1 in transrefl.pr2 x0

(** val coq_OrderedSet_isantisymm :
    coq_OrderedSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType ->
    pr1hSet paths **)

let coq_OrderedSet_isantisymm x x0 y r s =
  let x1 = x.pr1 in
  let _po_ = x1.pr2 in let _i_ = _po_.pr2 in _i_.pr2 x0 y r s

(** val coq_OrderedSet_istotal :
    coq_OrderedSet -> pr1hSet -> pr1hSet -> hProptoType **)

let coq_OrderedSet_istotal x x0 y =
  x.pr2 x0 y

(** val isdeceq_isdec_ordering :
    coq_OrderedSet -> pr1hSet isdeceq -> isdec_ordering **)

let isdeceq_isdec_ordering x deceq x0 y =
  let tot = coq_OrderedSet_istotal x x0 y in
  let d = deceq x0 y in
  (match d with
   | Coq_ii1 _ ->
     Coq_ii1
       (let x1 = x.pr1 in
        let _po_ = x1.pr2 in
        let _i_ = _po_.pr2 in let transrefl = _i_.pr1 in transrefl.pr2 x0)
   | Coq_ii2 b ->
     let c =
       let d0 =
         isapropcoprod
           (propproperty (posetRelation (underlyingPoset x) x0 y))
           (propproperty (posetRelation (underlyingPoset x) y x0))
           (fun r s ->
           b
             (let x1 = x.pr1 in
              let _po_ = x1.pr2 in let _i_ = _po_.pr2 in _i_.pr2 x0 y r s))
       in
       squash_to_prop tot d0 (fun e -> e)
     in
     (match c with
      | Coq_ii1 a -> Coq_ii1 a
      | Coq_ii2 b0 ->
        Coq_ii2 (fun le -> b (coq_OrderedSet_isantisymm x x0 y le b0))))

(** val isfinite_isdec_ordering :
    coq_OrderedSet -> hProptoType -> isdec_ordering **)

let isfinite_isdec_ordering x i x0 y =
  isdeceq_isdec_ordering x (isfinite_isdeceq i) x0 y

(** val isdeceq_isdec_lessthan :
    coq_OrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType
    decidable **)

let isdeceq_isdec_lessthan x i x0 y =
  decidable_ishinh
    (decidable_dirprod (isdeceq_isdec_ordering x i x0 y)
      (let x1 =
         isdecpropif (setproperty (carrierofposet (underlyingPoset x)) x0 y)
           (i x0 y)
       in
       (neg_isdecprop x1).pr1))

(** val isfinite_isdec_lessthan :
    coq_OrderedSet -> hProptoType -> pr1hSet -> pr1hSet -> hProptoType
    decidable **)

let isfinite_isdec_lessthan x i x0 y =
  isdeceq_isdec_lessthan x (isfinite_isdeceq i) x0 y

(** val isincl_underlyingPoset : (coq_OrderedSet, coq_Poset) isincl **)

let isincl_underlyingPoset =
  isinclpr1 (fun x -> isaprop_istotal (carrierofposet x) (posetRelation x))

(** val underlyingPoset_weq :
    coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths, coq_Poset
    paths) weq **)

let underlyingPoset_weq x y =
  make_weq (maponpaths underlyingPoset x y)
    (isweqonpathsincl underlyingPoset isincl_underlyingPoset x y)

(** val smallestUniqueness :
    coq_OrderedSet -> pr1hSet -> pr1hSet -> isSmallest -> isSmallest ->
    pr1hSet paths **)

let smallestUniqueness x x0 y i j =
  let q = coq_OrderedSet_istotal x x0 y in
  squash_to_prop q (setproperty (carrierofposet (underlyingPoset x)) x0 y)
    (fun c ->
    match c with
    | Coq_ii1 a -> coq_OrderedSet_isantisymm x x0 y a (j x0)
    | Coq_ii2 b -> coq_OrderedSet_isantisymm x x0 y (i y) b)

(** val biggestUniqueness :
    coq_OrderedSet -> pr1hSet -> pr1hSet -> isBiggest -> isBiggest -> pr1hSet
    paths **)

let biggestUniqueness x x0 y i j =
  let q = coq_OrderedSet_istotal x x0 y in
  squash_to_prop q (setproperty (carrierofposet (underlyingPoset x)) x0 y)
    (fun c ->
    match c with
    | Coq_ii1 a -> coq_OrderedSet_isantisymm x x0 y a (i y)
    | Coq_ii2 b -> coq_OrderedSet_isantisymm x x0 y (j x0) b)

(** val coq_OrderedSet_univalence :
    coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths,
    coq_PosetEquivalence) weq **)

let coq_OrderedSet_univalence x y =
  weqcomp (underlyingPoset_weq x y)
    (coq_Poset_univalence (underlyingPoset x) (underlyingPoset y))

(** val coq_OrderedSetEquivalence_rect :
    coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths -> 'a1) ->
    coq_PosetEquivalence -> 'a1 **)

let coq_OrderedSetEquivalence_rect x y ih f =
  let p = ih (invmap (coq_OrderedSet_univalence x y) f) in
  let h = homotweqinvweq (coq_OrderedSet_univalence x y) f in
  transportf
    (pr1weq (coq_OrderedSet_univalence x y)
      (invmap (coq_OrderedSet_univalence x y) f)) f h p

type coq_FiniteOrderedSet = (coq_OrderedSet, hProptoType) total2

(** val underlyingOrderedSet : coq_FiniteOrderedSet -> coq_OrderedSet **)

let underlyingOrderedSet x =
  x.pr1

(** val finitenessProperty : coq_FiniteOrderedSet -> hProptoType **)

let finitenessProperty x =
  x.pr2

(** val underlyingFiniteSet : coq_FiniteOrderedSet -> coq_FiniteSet **)

let underlyingFiniteSet x =
  { pr1 = __; pr2 = (finitenessProperty x) }

(** val istotal_FiniteOrderedSet : coq_FiniteOrderedSet -> pr1hSet istotal **)

let istotal_FiniteOrderedSet x =
  x.pr1.pr2

(** val coq_FiniteOrderedSet_isdeceq :
    coq_FiniteOrderedSet -> pr1hSet isdeceq **)

let coq_FiniteOrderedSet_isdeceq x =
  isfinite_isdeceq (finitenessProperty x)

(** val coq_FiniteOrderedSet_isdec_ordering :
    coq_FiniteOrderedSet -> isdec_ordering **)

let coq_FiniteOrderedSet_isdec_ordering x =
  isfinite_isdec_ordering (underlyingOrderedSet x) (finitenessProperty x)

(** val coq_FiniteOrderedSetDecidableOrdering :
    coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation **)

let coq_FiniteOrderedSetDecidableOrdering x x0 y =
  decidable_to_DecidableProposition
    (posetRelation (underlyingPoset (underlyingOrderedSet x)) x0 y)
    (coq_FiniteOrderedSet_isdec_ordering x x0 y)

(** val coq_FiniteOrderedSetDecidableEquality :
    coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation **)

let coq_FiniteOrderedSetDecidableEquality x x0 y =
  decidable_to_DecidableProposition
    (eqset (carrierofposet (underlyingPoset (underlyingOrderedSet x))) x0 y)
    (Obj.magic coq_FiniteOrderedSet_isdeceq x x0 y)

(** val coq_FiniteOrderedSetDecidableInequality :
    coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation **)

let coq_FiniteOrderedSetDecidableInequality x x0 y =
  decidable_to_DecidableProposition hneg
    (let x1 = fun x1 -> (neg_isdecprop x1).pr1 in
     Obj.magic x1
       (decidable_to_isdecprop_2
         (setproperty
           (carrierofposet (underlyingPoset (underlyingOrderedSet x))) x0 y)
         (coq_FiniteOrderedSet_isdeceq x x0 y)))

(** val coq_FiniteOrderedSetDecidableLessThan :
    coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation **)

let coq_FiniteOrderedSetDecidableLessThan x x0 y =
  decidable_to_DecidableProposition
    (coq_Poset_lessthan (underlyingPoset (underlyingOrderedSet x)) x0 y)
    (isfinite_isdec_lessthan (underlyingOrderedSet x) (finitenessProperty x)
      x0 y)

(** val coq_FiniteOrderedSet_segment :
    coq_FiniteOrderedSet -> pr1hSet -> coq_FiniteSet **)

let coq_FiniteOrderedSet_segment x x0 =
  subsetFiniteSet (underlyingFiniteSet x) (fun y ->
    coq_FiniteOrderedSetDecidableLessThan x y x0)

(** val height : coq_FiniteOrderedSet -> pr1hSet -> nat **)

let height x x0 =
  cardinalityFiniteSet (coq_FiniteOrderedSet_segment x x0)

(** val standardFiniteOrderedSet : nat -> coq_FiniteOrderedSet **)

let standardFiniteOrderedSet n =
  { pr1 = { pr1 = (stnposet n); pr2 = (fun x y ->
    istotalnatleh (stntonat n (Obj.magic x)) (stntonat n (Obj.magic y))) };
    pr2 = (isfinitestn n) }

(** val inducedPartialOrder :
    ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> 'a2 hrel -> 'a2 isPartialOrder
    -> 'a1 isPartialOrder **)

let inducedPartialOrder f incl _ po =
  { pr1 = { pr1 = (fun x y z a b -> po.pr1.pr1 (f x) (f y) (f z) a b); pr2 =
    (fun x -> po.pr1.pr2 (f x)) }; pr2 = (fun x y a b ->
    let x0 = fun x0 x' y0 -> (incl x0 x' y0).pr1 in
    let y0 = po.pr2 (f x) (f y) a b in (x0 x y y0).pr1) }

(** val inducedPartialOrder_weq :
    ('a1, 'a2) weq -> 'a2 hrel -> 'a2 isPartialOrder -> 'a1 isPartialOrder **)

let inducedPartialOrder_weq f r po =
  inducedPartialOrder (pr1weq f)
    (pr1weq (incl_injectivity (pr1weq f))
      (isinclweq (pr1weq f) (weqproperty f))) r po

(** val transportFiniteOrdering :
    nat -> ('a1, pr1hSet) weq -> coq_FiniteOrderedSet **)

let transportFiniteOrdering n w =
  { pr1 = { pr1 = { pr1 = { pr1 = __; pr2 =
    (Obj.magic isofhlevelweqb (S (S O)) w
      (setproperty
        (carrierofposet
          (underlyingPoset
            (underlyingOrderedSet (standardFiniteOrderedSet n)))))) }; pr2 =
    { pr1 = (fun x y ->
    coq_DecidableProposition_to_hProp
      (coq_FiniteOrderedSetDecidableOrdering (standardFiniteOrderedSet n)
        (pr1weq (Obj.magic w) x) (pr1weq (Obj.magic w) y))); pr2 =
    (inducedPartialOrder_weq (Obj.magic w)
      (posetRelation
        (underlyingPoset (underlyingOrderedSet (standardFiniteOrderedSet n))))
      (standardFiniteOrderedSet n).pr1.pr1.pr2.pr2) } }; pr2 = (fun x y ->
    (standardFiniteOrderedSet n).pr1.pr2 (pr1weq (Obj.magic w) x)
      (pr1weq (Obj.magic w) y)) }; pr2 =
    (isfiniteweqb w (standardFiniteOrderedSet n).pr2) }

(** val lexicographicOrder :
    hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
    pr1hSet hrel **)

let lexicographicOrder _ _ _ _ _ _ =
  hdisj

(** val lex_isrefl :
    hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
    (pr1hSet -> pr1hSet isrefl) -> pr1hSet isrefl **)

let lex_isrefl _ _ _ _ srefl u =
  let x = (Obj.magic u).pr1 in
  let y = (Obj.magic u).pr2 in
  hdisj_in2 { pr1 = Coq_paths_refl; pr2 = (srefl x y) }

(** val lex_istrans :
    hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
    pr1hSet isantisymm -> pr1hSet istrans -> (pr1hSet -> pr1hSet istrans) ->
    pr1hSet istrans **)

let lex_istrans x y r s _ rtrans strans u u' u'' p q =
  let x0 = (Obj.magic u).pr1 in
  let y0 = (Obj.magic u).pr2 in
  let x' = (Obj.magic u').pr1 in
  let y' = (Obj.magic u').pr2 in
  let x'' = (Obj.magic u'').pr1 in
  let y'' = (Obj.magic u'').pr2 in
  Obj.magic p
    (lexicographicOrder x y r s (Obj.magic { pr1 = x0; pr2 = y0 })
      (Obj.magic { pr1 = x''; pr2 = y'' })) (fun p0 ->
    match p0 with
    | Coq_ii1 a ->
      let pn = a.pr1 in
      let pl = a.pr2 in
      Obj.magic q
        (lexicographicOrder x y r s (Obj.magic { pr1 = x0; pr2 = y0 })
          (Obj.magic { pr1 = x''; pr2 = y'' })) (fun q0 ->
        match q0 with
        | Coq_ii1 a0 ->
          hinhpr
            (let ql = a0.pr2 in
             Coq_ii1 { pr1 = (fun _ -> assert false (* absurd case *)); pr2 =
             (rtrans x0 x' x'' pl ql) })
        | Coq_ii2 _ -> hinhpr (Coq_ii1 { pr1 = pn; pr2 = pl }))
    | Coq_ii2 b ->
      let s0 = b.pr2 in
      Obj.magic q
        (lexicographicOrder x y r s (Obj.magic { pr1 = x0; pr2 = y0 })
          (Obj.magic { pr1 = x''; pr2 = y'' })) (fun q0 ->
        match q0 with
        | Coq_ii1 a ->
          let n = a.pr1 in let r0 = a.pr2 in hdisj_in1 { pr1 = n; pr2 = r0 }
        | Coq_ii2 b0 ->
          let s' = b0.pr2 in
          hdisj_in2 { pr1 = Coq_paths_refl; pr2 =
            (strans x0 y0 y' y'' s0 s') }))

(** val lex_isantisymm :
    hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
    pr1hSet isantisymm -> (pr1hSet -> pr1hSet isantisymm) -> pr1hSet
    isantisymm **)

let lex_isantisymm x y _ _ _ _ u u' a b =
  let x0 = (Obj.magic u).pr1 in
  let y0 = (Obj.magic u).pr2 in
  let x' = (Obj.magic u').pr1 in
  let y' = (Obj.magic u').pr2 in
  squash_to_prop a
    (isaset_total2_hSet x y { pr1 = x0; pr2 = y0 } { pr1 = x'; pr2 = y' })
    (fun a0 ->
    squash_to_prop b
      (isaset_total2_hSet x y { pr1 = x0; pr2 = y0 } { pr1 = x'; pr2 = y' })
      (fun b0 ->
      match a0 with
      | Coq_ii1 _ -> assert false (* absurd case *)
      | Coq_ii2 _ ->
        (match b0 with
         | Coq_ii1 _ -> assert false (* absurd case *)
         | Coq_ii2 _ -> Coq_paths_refl)))

(** val lex_istotal :
    hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
    pr1hSet isdeceq -> pr1hSet istotal -> (pr1hSet -> pr1hSet istotal) ->
    pr1hSet istotal **)

let lex_istotal _ _ _ _ xdec rtot stot u u' =
  let x = (Obj.magic u).pr1 in
  let y = (Obj.magic u).pr2 in
  let x' = (Obj.magic u').pr1 in
  let y' = (Obj.magic u').pr2 in
  let d = xdec x x' in
  (match d with
   | Coq_ii1 a ->
     Obj.magic stot x' (transportf x x' a y) y' hdisj (fun p ->
       match p with
       | Coq_ii1 a0 -> hdisj_in1 (hdisj_in2 { pr1 = a; pr2 = a0 })
       | Coq_ii2 b -> hdisj_in2 (hdisj_in2 { pr1 = Coq_paths_refl; pr2 = b }))
   | Coq_ii2 b ->
     Obj.magic rtot x x' hdisj (fun p ->
       match p with
       | Coq_ii1 a -> hdisj_in1 (hdisj_in1 { pr1 = b; pr2 = a })
       | Coq_ii2 b0 ->
         hdisj_in2
           (hdisj_in1 { pr1 = (funcomp (pathsinv0 x' x) b); pr2 = b0 })))

(** val concatenateFiniteOrderedSets :
    coq_FiniteOrderedSet -> (pr1hSet -> coq_FiniteOrderedSet) ->
    coq_FiniteOrderedSet **)

let concatenateFiniteOrderedSets x y =
  { pr1 = { pr1 = { pr1 =
    (total2_hSet (carrierofposet (underlyingPoset (underlyingOrderedSet x)))
      (fun x0 ->
      carrierofposet (underlyingPoset (underlyingOrderedSet (y x0))))); pr2 =
    { pr1 =
    (lexicographicOrder
      (carrierofposet (underlyingPoset (underlyingOrderedSet x))) (fun x0 ->
      carrierofposet (underlyingPoset (underlyingOrderedSet (y x0))))
      (posetRelation (underlyingPoset (underlyingOrderedSet x))) (fun x0 ->
      posetRelation (underlyingPoset (underlyingOrderedSet (y x0))))); pr2 =
    { pr1 = { pr1 =
    (lex_istrans (carrierofposet (underlyingPoset (underlyingOrderedSet x)))
      (fun x0 ->
      carrierofposet (underlyingPoset (underlyingOrderedSet (y x0))))
      (posetRelation (underlyingPoset (underlyingOrderedSet x))) (fun x0 ->
      posetRelation (underlyingPoset (underlyingOrderedSet (y x0))))
      (isantisymm_posetRelation (underlyingPoset (underlyingOrderedSet x)))
      (istrans_posetRelation (underlyingPoset (underlyingOrderedSet x)))
      (fun x0 ->
      istrans_posetRelation (underlyingPoset (underlyingOrderedSet (y x0)))));
    pr2 =
    (lex_isrefl (carrierofposet (underlyingPoset (underlyingOrderedSet x)))
      (fun x0 ->
      carrierofposet (underlyingPoset (underlyingOrderedSet (y x0))))
      (posetRelation (underlyingPoset (underlyingOrderedSet x))) (fun x0 ->
      posetRelation (underlyingPoset (underlyingOrderedSet (y x0))))
      (fun x0 ->
      isrefl_posetRelation (underlyingPoset (underlyingOrderedSet (y x0))))) };
    pr2 =
    (lex_isantisymm
      (carrierofposet (underlyingPoset (underlyingOrderedSet x))) (fun x0 ->
      carrierofposet (underlyingPoset (underlyingOrderedSet (y x0))))
      (posetRelation (underlyingPoset (underlyingOrderedSet x))) (fun x0 ->
      posetRelation (underlyingPoset (underlyingOrderedSet (y x0))))
      (isantisymm_posetRelation (underlyingPoset (underlyingOrderedSet x)))
      (fun x0 ->
      isantisymm_posetRelation (underlyingPoset (underlyingOrderedSet (y x0))))) } } };
    pr2 =
    (lex_istotal (carrierofposet (underlyingPoset (underlyingOrderedSet x)))
      (fun x0 ->
      carrierofposet (underlyingPoset (underlyingOrderedSet (y x0))))
      (posetRelation (underlyingPoset (underlyingOrderedSet x))) (fun x0 ->
      posetRelation (underlyingPoset (underlyingOrderedSet (y x0))))
      (coq_FiniteOrderedSet_isdeceq x) (istotal_FiniteOrderedSet x)
      (fun x0 -> istotal_FiniteOrderedSet (y x0))) }; pr2 =
    (isfinitetotal2 (finitenessProperty x) (fun x0 ->
      finitenessProperty (y x0))) }

type coq_FiniteStructure = (nat, coq_PosetEquivalence) total2

type isLattice =
  (pr1hSet isPartialOrder, (pr1hSet -> pr1hSet -> pr1hSet -> (hProptoType,
  hProptoType) logeq, (pr1hSet -> pr1hSet -> pr1hSet -> (hProptoType,
  hProptoType) logeq, coq_unit) total2) total2) total2

type istrans2 =
  (pr1hSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType ->
  hProptoType, (pr1hSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType
  -> hProptoType, coq_unit) total2) total2

type 'x iswklin = 'x -> 'x -> 'x -> hProptoType -> hProptoType

type isComputablyOrdered =
  (isLattice, (istrans2, (pr1hSet istrans, (pr1hSet isirrefl, (pr1hSet
  iscotrans, coq_unit) total2) total2) total2) total2) total2

(** val apart_isirrefl :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> pr1hSet isirrefl **)

let apart_isirrefl _ _ _ _ ic =
  let pr3 = ic.pr2 in
  let pr4 = pr3.pr2 in
  let pr5 = pr4.pr2 in
  let irrefl = pr5.pr1 in
  (fun x a ->
  Obj.magic a hfalse (fun b ->
    match b with
    | Coq_ii1 a0 -> irrefl x a0
    | Coq_ii2 b0 -> irrefl x b0))

(** val lt_implies_le :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType **)

let lt_implies_le _ _ _ _ ic x y l =
  Obj.magic (fun m ->
    let pr3 = ic.pr2 in
    let pr4 = pr3.pr2 in
    let translt = pr4.pr1 in
    let pr5 = pr4.pr2 in
    let irrefl = pr5.pr1 in let n = translt x y x l m in irrefl x n)

(** val apart_implies_ne :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths
    neg **)

let apart_implies_ne x lt min max ic x0 _ a _ =
  apart_isirrefl x lt min max ic x0 a

(** val tightness :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> pr1hSet -> pr1hSet -> (hProptoType, hProptoType)
    logeq **)

let tightness x lt min max ic x0 y =
  let pr3 = ic.pr1 in
  let pr4 = pr3.pr1 in
  let antisymmle = pr4.pr2 in
  { pr1 = (fun m ->
  let p = fromnegcoprod_prop (lt y x0) (lt x0 y) m in
  let p0 = (Obj.magic p).pr1 in
  let q = (Obj.magic p).pr2 in Obj.magic antisymmle x0 y p0 q); pr2 =
  (fun _ -> Obj.magic apart_isirrefl x lt min max ic x0) }

(** val ne_implies_dnegapart :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> pr1hSet -> pr1hSet -> pr1hSet paths neg ->
    hProptoType dneg **)

let ne_implies_dnegapart x lt min max ic x0 y n m =
  n
    (let x1 = fun x1 y0 -> (tightness x lt min max ic x1 y0).pr1 in
     Obj.magic x1 x0 y m)

(** val ne_implies_apart :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> hProptoType -> pr1hSet -> pr1hSet -> pr1hSet paths
    neg -> hProptoType **)

let ne_implies_apart x lt min max ic =
  let apart = fun _ _ -> hdisj in
  (fun lem x0 y a ->
  dneg_LEM (apart x0 y) lem (ne_implies_dnegapart x lt min max ic x0 y a))

(** val trichotomy :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> hProptoType -> pr1hSet -> pr1hSet -> hProptoType **)

let trichotomy x lt min max ic lem x0 y =
  let h = Obj.magic lem (eqset x x0 y) in
  (match h with
   | Coq_ii1 a -> hdisj_in2 (hdisj_in1 a)
   | Coq_ii2 b ->
     let l = ne_implies_apart x lt min max ic lem x0 y b in
     Obj.magic l hdisj (fun m ->
       match m with
       | Coq_ii1 a -> hdisj_in2 (hdisj_in2 a)
       | Coq_ii2 b0 -> hdisj_in1 b0))

(** val le_istotal :
    hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
    isComputablyOrdered -> hProptoType -> pr1hSet istotal **)

let le_istotal x lt min max ic lem x0 y =
  let m = trichotomy x lt min max ic lem x0 y in
  Obj.magic m hdisj (fun m0 ->
    match m0 with
    | Coq_ii1 a -> hdisj_in1 (lt_implies_le x lt min max ic x0 y a)
    | Coq_ii2 b ->
      b hdisj (fun m1 ->
        match m1 with
        | Coq_ii1 _ ->
          hdisj_in1
            (let pr3 = ic.pr2 in
             let pr4 = pr3.pr2 in let pr5 = pr4.pr2 in pr5.pr1 x0)
        | Coq_ii2 b0 -> hdisj_in2 (lt_implies_le x lt min max ic y x0 b0)))
