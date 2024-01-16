open NaturalNumbers
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets

type __ = Obj.t

val retract_dec :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2, 'a2) homot -> 'a1 isdeceq -> 'a2
  isdeceq

val logeq_dec : ('a1, 'a2) logeq -> 'a1 decidable -> 'a2 decidable

val decidable_prop : hProp -> hProp

val coq_LEM : hProp

type coq_ComplementaryPair =
  (coq_UU, (coq_UU, (__, __) complementary) total2) total2

type coq_Part1 = __

type coq_Part2 = __

val pair_contradiction :
  coq_ComplementaryPair -> coq_Part1 -> coq_Part2 -> empty

val chooser : coq_ComplementaryPair -> (coq_Part1, coq_Part2) coprod

type isTrue = (coq_Part1, (coq_Part1, coq_Part2) coprod) hfiber

type isFalse = (coq_Part2, (coq_Part1, coq_Part2) coprod) hfiber

val trueWitness : coq_ComplementaryPair -> isTrue -> coq_Part1

val falseWitness : coq_ComplementaryPair -> isFalse -> coq_Part2

val complementaryDecisions :
  coq_ComplementaryPair -> (isTrue, isFalse) coprod iscontr

val isaprop_isTrue : coq_ComplementaryPair -> isTrue isaprop

val isaprop_isFalse : coq_ComplementaryPair -> isFalse isaprop

val pair_truth : coq_ComplementaryPair -> coq_Part1 -> isTrue

val pair_falsehood : coq_ComplementaryPair -> coq_Part2 -> isFalse

val to_ComplementaryPair : ('a1, 'a1 neg) coprod -> coq_ComplementaryPair

type 'x isolation = isFalse

val isaprop_isolation : 'a1 -> 'a1 isisolated -> 'a1 -> 'a1 isolation isaprop

val isolation_to_inequality :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 isolation -> 'a1 paths neg

val inequality_to_isolation :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths neg -> 'a1 isolation

val pairNegation : coq_ComplementaryPair -> coq_ComplementaryPair

val pairConjunction :
  coq_ComplementaryPair -> coq_ComplementaryPair -> coq_ComplementaryPair

val pairDisjunction :
  coq_ComplementaryPair -> coq_ComplementaryPair -> coq_ComplementaryPair

val dnegelim : ('a1, 'a2) complementary -> 'a1 dneg -> 'a1

val coq_LEM_for_sets : hProptoType -> 'a1 isaset -> 'a1 isdeceq

val isaprop_LEM : hProptoType isaprop

val dneg_LEM : hProp -> hProptoType -> hProptoType dneg -> hProptoType

val reversal_LEM :
  hProp -> hProp -> hProptoType -> (hProptoType neg -> hProptoType) ->
  hProptoType neg -> hProptoType

type coq_DecidableProposition = (coq_UU, __ isdecprop) total2

val isdecprop_to_DecidableProposition :
  'a1 isdecprop -> coq_DecidableProposition

val decidable_to_isdecprop :
  hProp -> hProptoType decidable -> hProptoType isdecprop

val decidable_to_isdecprop_2 :
  'a1 isaprop -> ('a1, 'a1 neg) coprod -> 'a1 isdecprop

val decidable_to_DecidableProposition :
  hProp -> hProptoType decidable -> coq_DecidableProposition

val coq_DecidableProposition_to_isdecprop :
  coq_DecidableProposition -> __ isdecprop

val coq_DecidableProposition_to_hProp : coq_DecidableProposition -> hProp

val decidabilityProperty : coq_DecidableProposition -> hProptoType isdecprop

type 'x coq_DecidableSubtype = 'x -> coq_DecidableProposition

type 'x coq_DecidableRelation = 'x -> 'x -> coq_DecidableProposition

val decrel_to_DecidableRelation : 'a1 decrel -> 'a1 coq_DecidableRelation

val decidableAnd :
  coq_DecidableProposition -> coq_DecidableProposition ->
  coq_DecidableProposition

val decidableOr :
  coq_DecidableProposition -> coq_DecidableProposition ->
  coq_DecidableProposition

val neg_isdecprop : 'a1 isdecprop -> 'a1 neg isdecprop

val decidableNot : coq_DecidableProposition -> coq_DecidableProposition

val choice : coq_DecidableProposition -> 'a1 -> 'a1 -> 'a1

val dependent_choice :
  coq_DecidableProposition -> (hProptoType -> 'a1) -> (hProptoType neg ->
  'a1) -> 'a1

val choice_compute_yes :
  coq_DecidableProposition -> hProptoType -> 'a1 -> 'a1 -> 'a1 paths

val choice_compute_no :
  coq_DecidableProposition -> hProptoType neg -> 'a1 -> 'a1 -> 'a1 paths

type 'x decidableSubtypeCarrier = ('x, hProptoType) total2

type 'x decidableSubtypeCarrier' = ('x, bool) hfiber

val decidableSubtypeCarrier_weq :
  'a1 coq_DecidableSubtype -> ('a1 decidableSubtypeCarrier', 'a1
  decidableSubtypeCarrier) weq

val coq_DecidableSubtype_to_hsubtype :
  'a1 coq_DecidableSubtype -> 'a1 hsubtype

val coq_DecidableRelation_to_hrel : 'a1 coq_DecidableRelation -> 'a1 hrel

val natlth_DecidableProposition : nat coq_DecidableRelation

val natleh_DecidableProposition : nat coq_DecidableRelation

val natgth_DecidableProposition : nat coq_DecidableRelation

val natgeh_DecidableProposition : nat coq_DecidableRelation

val nateq_DecidableProposition : nat coq_DecidableRelation

val natneq_DecidableProposition : nat coq_DecidableRelation
