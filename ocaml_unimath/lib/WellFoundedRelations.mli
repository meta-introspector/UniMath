open NaturalNumbers
open PartA
open PartD
open Preamble
open Propositions
open Propositions0
open Univalence
open UnivalenceAxiom

type __ = Obj.t

type ('x, 'lt, 'p) hereditary = 'x -> ('x -> 'lt -> 'p) -> 'p

type ('x, 'lt) strongly_well_founded =
  __ -> ('x, 'lt, __) hereditary -> ('x -> __, 'x -> __ paths) total2

type ('x, 'lt) weakly_well_founded =
  ('x -> hProp) -> ('x, 'lt, hProptoType) hereditary -> 'x -> hProptoType

type ('x, 'lt) chain = __

type ('x, 'lt) le = (nat, ('x, 'lt) chain) total2

val nil : 'a1 -> ('a1, 'a2) le

val cons' :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) le -> 'a2 -> 'a1 paths -> ('a1, 'a2)
  le

val cons1 :
  nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) chain ->
  ('a1, 'a2) chain

val cons :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) le -> ('a1, 'a2)
  le

val coq_Unnamed_thm :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) le
  -> 'a2 -> 'a1 paths -> ('a1, 'a2) le paths

type ('x, 'lt, 'p) guided_by = 'x -> ('x, 'lt) le -> 'p paths

type ('x, 'lt, 'p) attempt =
  ('x -> ('x, 'lt) le -> 'p, ('x, 'lt, 'p) guided_by) total2

val attempt_fun :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> 'a1 ->
  ('a1, 'a2) le -> 'a3

val attempt_comp :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) guided_by

val disassemble_attempt :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> 'a1 -> 'a1
  -> 'a2 -> 'a1 paths -> ('a1, 'a2, 'a3) attempt

val assemble_attempt :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1 -> 'a1 -> 'a2 -> 'a1 paths ->
  ('a1, 'a2, 'a3) attempt) -> ('a1, 'a2, 'a3) attempt

val attempt_lemma :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) attempt -> (('a1 -> ('a1, 'a2) le -> 'a3) paths -> 'a4) -> ('a1 ->
  ('a1, 'a2) le -> 'a3 paths) -> 'a4

val attempt_paths :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) attempt -> ('a1 -> ('a1, 'a2) le -> 'a3 paths) -> ('a1 -> ('a1, 'a2)
  le -> 'a3 paths paths) -> ('a1, 'a2, 'a3) attempt paths

val assemble_disassemble :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) attempt paths

val iscontr_attempt :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 ->
  ('a1, 'a2, 'a3) attempt iscontr

val the_attempt :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 ->
  ('a1, 'a2, 'a3) attempt

val the_value :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a3

val the_comp :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a3
  paths

val strongly_from_weakly_well_founded :
  ('a1, 'a2) weakly_well_founded -> ('a1, 'a2, __) hereditary -> ('a1 -> __,
  'a1 -> __ paths) total2

val irrefl : ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a2 neg

val notboth : ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a1 -> 'a2 -> 'a2 neg

val diagRecursion :
  (nat -> 'a1) -> (nat -> nat -> 'a1 -> 'a1) -> nat -> nat -> 'a1

val chaintrans :
  'a1 -> 'a1 -> 'a1 -> nat -> nat -> ('a1, 'a2) chain -> ('a1, 'a2) chain ->
  ('a1, 'a2) chain
