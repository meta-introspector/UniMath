open DecidablePropositions
open NaturalNumbers
open NegativePropositions
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open StandardFiniteSets
open Subtypes

type 'x nelstruct = (stn, 'x) weq

val nelstructToFunction : nat -> 'a1 nelstruct -> stn -> 'a1

val nelstructonstn : nat -> stn nelstruct

val nelstructweqf : nat -> ('a1, 'a2) weq -> 'a1 nelstruct -> 'a2 nelstruct

val nelstructweqb : nat -> ('a1, 'a2) weq -> 'a2 nelstruct -> 'a1 nelstruct

val nelstructonempty : empty nelstruct

val nelstructonempty2 : 'a1 neg -> 'a1 nelstruct

val nelstructonunit : coq_unit nelstruct

val nelstructoncontr : 'a1 iscontr -> 'a1 nelstruct

val nelstructonbool : bool nelstruct

val nelstructoncoprodwithunit :
  nat -> 'a1 nelstruct -> ('a1, coq_unit) coprod nelstruct

val nelstructoncompl : nat -> 'a1 -> 'a1 nelstruct -> 'a1 compl nelstruct

val nelstructoncoprod :
  nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1, 'a2) coprod nelstruct

val nelstructontotal2 :
  nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1,
  'a2) total2 nelstruct

val nelstructondirprod :
  nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1, 'a2) dirprod nelstruct

val nelstructonfun :
  nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1 -> 'a2) nelstruct

val nelstructonforall :
  nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1 ->
  'a2) nelstruct

val nelstructonweq : nat -> 'a1 nelstruct -> ('a1, 'a1) weq nelstruct

val isofnel : nat -> hProp

val isofneluniv :
  nat -> hProp -> ('a1 nelstruct -> hProptoType) -> hProptoType -> hProptoType

val isofnelstn : nat -> hProptoType

val isofnelweqf : nat -> ('a1, 'a2) weq -> hProptoType -> hProptoType

val isofnelweqb : nat -> ('a1, 'a2) weq -> hProptoType -> hProptoType

val isofnelempty : hProptoType

val isofnelempty2 : 'a1 neg -> hProptoType

val isofnelunit : hProptoType

val isofnelcontr : 'a1 iscontr -> hProptoType

val isofnelbool : hProptoType

val isofnelcoprodwithunit : nat -> hProptoType -> hProptoType

val isofnelcompl : nat -> 'a1 -> hProptoType -> hProptoType

val isofnelcoprod : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isofnelondirprod : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isofnelonfun : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isofnelonweq : nat -> hProptoType -> hProptoType

type 'x finstruct = (nat, 'x nelstruct) total2

val finstruct_cardinality : 'a1 finstruct -> nat

val finstructToFunction : 'a1 finstruct -> 'a1 nelstruct

val make_finstruct : nat -> (stn, 'a1) weq -> 'a1 finstruct

val finstructonstn : nat -> stn finstruct

val finstructweqf : ('a1, 'a2) weq -> 'a1 finstruct -> 'a2 finstruct

val finstructweqb : ('a1, 'a2) weq -> 'a2 finstruct -> 'a1 finstruct

val finstructonempty : empty finstruct

val finstructonempty2 : 'a1 neg -> 'a1 finstruct

val finstructonunit : coq_unit finstruct

val finstructoncontr : 'a1 iscontr -> 'a1 finstruct

val finstructonbool : bool finstruct

val finstructoncoprodwithunit :
  'a1 finstruct -> ('a1, coq_unit) coprod finstruct

val finstructoncompl : 'a1 -> 'a1 finstruct -> 'a1 compl finstruct

val finstructoncoprod :
  'a1 finstruct -> 'a2 finstruct -> ('a1, 'a2) coprod finstruct

val finstructontotal2 :
  'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1, 'a2) total2 finstruct

val finstructondirprod :
  'a1 finstruct -> 'a2 finstruct -> ('a1, 'a2) dirprod finstruct

val finstructondecsubset :
  ('a1 -> bool) -> 'a1 finstruct -> ('a1, bool) hfiber finstruct

val finstructonfun : 'a1 finstruct -> 'a2 finstruct -> ('a1 -> 'a2) finstruct

val finstructonforall :
  'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1 -> 'a2) finstruct

val finstructonweq : 'a1 finstruct -> ('a1, 'a1) weq finstruct

val isfinite : hProp

val isfinite_isdeceq : hProptoType -> 'a1 isdeceq

val isfinite_isaset : hProptoType -> 'a1 isaset

val fincard : hProptoType -> nat

val ischoicebasefiniteset : hProptoType -> hProptoType

val isfinitestn : nat -> hProptoType

val isfiniteweqf : ('a1, 'a2) weq -> hProptoType -> hProptoType

val isfiniteweqb : ('a1, 'a2) weq -> hProptoType -> hProptoType

val isfiniteempty : hProptoType

val isfiniteempty2 : 'a1 neg -> hProptoType

val isfiniteunit : hProptoType

val isfinitecontr : 'a1 iscontr -> hProptoType

val isfinitebool : hProptoType

val isfinitecoprodwithunit : hProptoType -> hProptoType

val isfinitecompl : 'a1 -> hProptoType -> hProptoType

val isfinitecoprod : hProptoType -> hProptoType -> hProptoType

val isfinitetotal2 : hProptoType -> ('a1 -> hProptoType) -> hProptoType

val isfinitedirprod : hProptoType -> hProptoType -> hProptoType

val isfinitedecsubset : ('a1 -> bool) -> hProptoType -> hProptoType

val isfinitefun : hProptoType -> hProptoType -> hProptoType

val isfiniteforall : hProptoType -> ('a1 -> hProptoType) -> hProptoType

val isfiniteweq : hProptoType -> hProptoType

