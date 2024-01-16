open PartA
open Preamble
open Propositions
open Sets
open StandardFiniteSets

type 'x nelstruct = (stn, 'x) weq

val nelstructToFunction : nat -> 'a1 nelstruct -> stn -> 'a1

val nelstructonstn : nat -> stn nelstruct

val nelstructontotal2 :
  nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1,
  'a2) total2 nelstruct

type 'x finstruct = (nat, 'x nelstruct) total2

val finstruct_cardinality : 'a1 finstruct -> nat

val finstructToFunction : 'a1 finstruct -> 'a1 nelstruct

val make_finstruct : nat -> (stn, 'a1) weq -> 'a1 finstruct

val finstructonstn : nat -> stn finstruct

val finstructontotal2 :
  'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1, 'a2) total2 finstruct

val ischoicebasefiniteset : hProptoType -> hProptoType

val isfinitestn : nat -> hProptoType

val isfinitetotal2 : hProptoType -> ('a1 -> hProptoType) -> hProptoType

type coq_FiniteSet = (coq_UU, hProptoType) total2

val isfinite_to_FiniteSet : hProptoType -> coq_FiniteSet

val coq_FiniteSetSum :
  coq_FiniteSet -> (pr1hSet -> coq_FiniteSet) -> coq_FiniteSet

val standardFiniteSet : nat -> coq_FiniteSet
