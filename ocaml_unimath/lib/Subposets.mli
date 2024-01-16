open PartB
open Preamble
open Propositions
open Sets

type coq_Subposet = pr1hSet hsubtype

type coq_Subposet' =
  (coq_Poset, (posetmorphism, (pr1hSet, pr1hSet) isincl) total2) total2

val coq_Subposet'_to_Poset : coq_Poset -> coq_Subposet' -> coq_Poset

val coq_Subposet_to_Subposet' : coq_Poset -> coq_Subposet -> coq_Subposet'

val coq_Subposet'_to_Subposet : coq_Poset -> coq_Subposet' -> coq_Subposet
