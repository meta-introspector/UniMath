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

val isTotalOrder : hSet -> pr1hSet hrel -> hProp

val tot_nge_to_le :
  hSet -> pr1hSet hrel -> pr1hSet istotal -> pr1hSet -> pr1hSet ->
  hProptoType -> hProptoType

val tot_nle_iff_gt :
  hSet -> pr1hSet hrel -> hProptoType -> pr1hSet -> pr1hSet -> (hProptoType,
  hProptoType) logeq

type isSmallest = pr1hSet -> hProptoType

type isBiggest = pr1hSet -> hProptoType

type isMinimal = pr1hSet -> hProptoType -> pr1hSet paths

type isMaximal = pr1hSet -> hProptoType -> pr1hSet paths

type consecutive =
  ((hProptoType, pr1hSet paths neg) dirprod, pr1hSet -> hProptoType) dirprod

val isaprop_isSmallest : coq_Poset -> pr1hSet -> isSmallest isaprop

val isaprop_isBiggest : coq_Poset -> pr1hSet -> isBiggest isaprop

val coq_Poset_univalence_map :
  coq_Poset -> coq_Poset -> coq_Poset paths -> coq_PosetEquivalence

val posetStructureIdentity :
  hSet -> coq_PartialOrder -> coq_PartialOrder -> (isPosetEquivalence,
  coq_PartialOrder paths) logeq

val posetTransport_weq :
  coq_Poset -> coq_Poset -> ((hSet, coq_PartialOrder) coq_PathPair,
  coq_PosetEquivalence) weq

val coq_Poset_univalence_0 :
  coq_Poset -> coq_Poset -> (coq_Poset paths, coq_PosetEquivalence) weq

val coq_Poset_univalence :
  coq_Poset -> coq_Poset -> (coq_Poset paths, coq_PosetEquivalence) weq

val coq_Poset_univalence_compute :
  coq_Poset -> coq_Poset -> coq_Poset paths -> coq_PosetEquivalence paths

val coq_PosetEquivalence_rect :
  coq_Poset -> coq_Poset -> (coq_Poset paths -> 'a1) -> coq_PosetEquivalence
  -> 'a1

val isMinimal_preserved :
  coq_Poset -> coq_Poset -> pr1hSet -> isMinimal -> coq_PosetEquivalence ->
  isMinimal

val isMaximal_preserved :
  coq_Poset -> coq_Poset -> pr1hSet -> isMaximal -> coq_PosetEquivalence ->
  isMaximal

val consecutive_preserved :
  coq_Poset -> coq_Poset -> pr1hSet -> pr1hSet -> consecutive ->
  coq_PosetEquivalence -> consecutive

type coq_OrderedSet = (coq_Poset, pr1hSet istotal) total2

val underlyingPoset : coq_OrderedSet -> coq_Poset

val coq_Poset_lessthan : coq_Poset -> pr1hSet -> pr1hSet -> hProp

val coq_OrderedSet_isrefl : coq_OrderedSet -> pr1hSet -> hProptoType

val coq_OrderedSet_isantisymm :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType ->
  pr1hSet paths

val coq_OrderedSet_istotal :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> hProptoType

val isdeceq_isdec_ordering :
  coq_OrderedSet -> pr1hSet isdeceq -> isdec_ordering

val isfinite_isdec_ordering : coq_OrderedSet -> hProptoType -> isdec_ordering

val isdeceq_isdec_lessthan :
  coq_OrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType
  decidable

val isfinite_isdec_lessthan :
  coq_OrderedSet -> hProptoType -> pr1hSet -> pr1hSet -> hProptoType decidable

val isincl_underlyingPoset : (coq_OrderedSet, coq_Poset) isincl

val underlyingPoset_weq :
  coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths, coq_Poset paths)
  weq

val smallestUniqueness :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> isSmallest -> isSmallest -> pr1hSet
  paths

val biggestUniqueness :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> isBiggest -> isBiggest -> pr1hSet
  paths

val coq_OrderedSet_univalence :
  coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths,
  coq_PosetEquivalence) weq

val coq_OrderedSetEquivalence_rect :
  coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths -> 'a1) ->
  coq_PosetEquivalence -> 'a1

type coq_FiniteOrderedSet = (coq_OrderedSet, hProptoType) total2

val underlyingOrderedSet : coq_FiniteOrderedSet -> coq_OrderedSet

val finitenessProperty : coq_FiniteOrderedSet -> hProptoType

val underlyingFiniteSet : coq_FiniteOrderedSet -> coq_FiniteSet

val istotal_FiniteOrderedSet : coq_FiniteOrderedSet -> pr1hSet istotal

val coq_FiniteOrderedSet_isdeceq : coq_FiniteOrderedSet -> pr1hSet isdeceq

val coq_FiniteOrderedSet_isdec_ordering :
  coq_FiniteOrderedSet -> isdec_ordering

val coq_FiniteOrderedSetDecidableOrdering :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSetDecidableEquality :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSetDecidableInequality :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSetDecidableLessThan :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSet_segment :
  coq_FiniteOrderedSet -> pr1hSet -> coq_FiniteSet

val height : coq_FiniteOrderedSet -> pr1hSet -> nat

val standardFiniteOrderedSet : nat -> coq_FiniteOrderedSet

val inducedPartialOrder :
  ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> 'a2 hrel -> 'a2 isPartialOrder ->
  'a1 isPartialOrder

val inducedPartialOrder_weq :
  ('a1, 'a2) weq -> 'a2 hrel -> 'a2 isPartialOrder -> 'a1 isPartialOrder

val transportFiniteOrdering :
  nat -> ('a1, pr1hSet) weq -> coq_FiniteOrderedSet

val lexicographicOrder :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet hrel

val lex_isrefl :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  (pr1hSet -> pr1hSet isrefl) -> pr1hSet isrefl

val lex_istrans :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet isantisymm -> pr1hSet istrans -> (pr1hSet -> pr1hSet istrans) ->
  pr1hSet istrans

val lex_isantisymm :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet isantisymm -> (pr1hSet -> pr1hSet isantisymm) -> pr1hSet isantisymm

val lex_istotal :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet isdeceq -> pr1hSet istotal -> (pr1hSet -> pr1hSet istotal) ->
  pr1hSet istotal

val concatenateFiniteOrderedSets :
  coq_FiniteOrderedSet -> (pr1hSet -> coq_FiniteOrderedSet) ->
  coq_FiniteOrderedSet

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

val apart_isirrefl :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet isirrefl

val lt_implies_le :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType

val apart_implies_ne :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths
  neg

val tightness :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> (hProptoType, hProptoType)
  logeq

val ne_implies_dnegapart :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> pr1hSet paths neg ->
  hProptoType dneg

val ne_implies_apart :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> hProptoType -> pr1hSet -> pr1hSet -> pr1hSet paths
  neg -> hProptoType

val trichotomy :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> hProptoType -> pr1hSet -> pr1hSet -> hProptoType

val le_istotal :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> hProptoType -> pr1hSet istotal
