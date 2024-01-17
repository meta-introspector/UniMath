open FiniteSets
open Lists
open NaturalNumbers
open PartA
open PartA0
open PartB
open PartD
open Preamble
open Propositions
open Sets
open StandardFiniteSets
open UnivalenceAxiom
open Vectors

type __ = Obj.t

type 'x coq_Vector = stn -> 'x

val vector_hlevel : nat -> nat -> 'a1 isofhlevel -> 'a1 coq_Vector isofhlevel

val const_vec : nat -> 'a1 -> 'a1 coq_Vector

val iscontr_vector_0 : 'a1 coq_Vector iscontr

val empty_vec : 'a1 coq_Vector

val weq_vector_1 : ('a1, 'a1 coq_Vector) weq

val append_vec : nat -> 'a1 coq_Vector -> 'a1 -> 'a1 coq_Vector

val append_vec_compute_1 : nat -> 'a1 coq_Vector -> 'a1 -> stn -> 'a1 paths

val append_vec_compute_2 : nat -> 'a1 coq_Vector -> 'a1 -> 'a1 paths

val drop_and_append_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Vector paths

val coq_Vector_rect :
  'a2 -> (nat -> 'a1 coq_Vector -> 'a1 -> 'a2 -> 'a2) -> nat -> 'a1
  coq_Vector -> 'a2

val vectorEquality :
  nat -> nat -> 'a1 coq_Vector -> 'a1 coq_Vector -> nat paths -> (stn -> 'a1
  paths) -> 'a1 coq_Vector paths

val tail : nat -> 'a1 coq_Vector -> 'a1 coq_Vector

val vector_stn_proofirrelevance :
  nat -> 'a1 coq_Vector -> stn -> stn -> nat paths -> 'a1 paths

type 'x coq_Matrix = 'x coq_Vector coq_Vector

val transpose : nat -> nat -> 'a1 coq_Matrix -> 'a1 coq_Matrix

val row : nat -> nat -> 'a1 coq_Matrix -> stn -> 'a1 coq_Vector

val col : nat -> nat -> 'a1 coq_Matrix -> stn -> 'a1 coq_Vector

val row_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Matrix

val col_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Matrix

val matrix_hlevel :
  nat -> nat -> nat -> 'a1 isofhlevel -> 'a1 coq_Matrix isofhlevel

val const_matrix : nat -> nat -> 'a1 -> 'a1 coq_Matrix

(* val weq_matrix_1_1 : ('a1, 'a1 coq_Matrix) weq *)

type 'x coq_Sequence = (nat, 'x coq_Vector) total2

type 'x coq_NonemptySequence = (nat, stn -> 'x) total2

type 'x coq_UnorderedSequence = (coq_FiniteSet, pr1hSet -> 'x) total2

val length : 'a1 coq_Sequence -> nat

val sequenceToFunction : 'a1 coq_Sequence -> stn -> 'a1

val unorderedSequenceToFunction : 'a1 coq_UnorderedSequence -> __ -> 'a1

val sequenceToUnorderedSequence :
  'a1 coq_Sequence -> 'a1 coq_UnorderedSequence

val length' : 'a1 coq_NonemptySequence -> nat

val functionToSequence : nat -> (stn -> 'a1) -> 'a1 coq_Sequence

val functionToUnorderedSequence :
  coq_FiniteSet -> (pr1hSet -> 'a1) -> 'a1 coq_UnorderedSequence

val coq_NonemptySequenceToFunction : 'a1 coq_NonemptySequence -> stn -> 'a1

val coq_NonemptySequenceToSequence :
  'a1 coq_NonemptySequence -> 'a1 coq_Sequence

val composeSequence : ('a1 -> 'a2) -> 'a1 coq_Sequence -> 'a2 coq_Sequence

val composeSequence' :
  nat -> nat -> (stn -> 'a1) -> (stn -> stn) -> 'a1 coq_Sequence

val composeUnorderedSequence :
  ('a1 -> 'a2) -> 'a1 coq_UnorderedSequence -> 'a2 coq_UnorderedSequence

val weqListSequence : ('a1 list, 'a1 coq_Sequence) weq

val transport_stn : nat -> nat -> nat -> hProptoType -> nat paths -> stn paths

val sequenceEquality2 :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (stn -> 'a1 paths) ->
  'a1 coq_Sequence paths

val seq_key_eq_lemma :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (nat -> hProptoType ->
  hProptoType -> 'a1 paths) -> 'a1 coq_Sequence paths

val seq_key_eq_lemma' :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (nat -> (hProptoType,
  (hProptoType, 'a1 paths) total2) total2) -> 'a1 coq_Sequence paths

val nil : 'a1 coq_Sequence

val append : 'a1 coq_Sequence -> 'a1 -> 'a1 coq_Sequence

val drop_and_append : nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths

val nil_unique : (stn -> 'a1) -> 'a1 coq_Sequence paths

val iscontr_rect' : 'a1 iscontr -> 'a1 -> 'a2 -> 'a1 -> 'a2

val iscontr_rect_compute' : 'a1 iscontr -> 'a1 -> 'a2 -> 'a2 paths

val iscontr_rect'' : 'a1 iscontr -> 'a2 -> 'a1 -> 'a2

val iscontr_rect_compute'' : 'a1 iscontr -> 'a2 -> 'a2 paths

val iscontr_adjointness : 'a1 iscontr -> 'a1 -> 'a1 paths paths

val iscontr_rect : 'a1 iscontr -> 'a1 -> 'a2 -> 'a1 -> 'a2

val iscontr_rect_compute : 'a1 iscontr -> 'a1 -> 'a2 -> 'a2 paths

val weqsecovercontr' : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq

val nil_length : 'a1 coq_Sequence -> (nat paths, 'a1 coq_Sequence paths) logeq

val drop : 'a1 coq_Sequence -> nat paths neg -> 'a1 coq_Sequence

val drop' : 'a1 coq_Sequence -> 'a1 coq_Sequence paths neg -> 'a1 coq_Sequence

val append_and_drop_fun : nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a1) paths

val drop_and_append' : nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths

val disassembleSequence :
  'a1 coq_Sequence -> (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod

val assembleSequence :
  (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod -> 'a1 coq_Sequence

val assembleSequence_ii2 :
  ('a1, 'a1 coq_Sequence) dirprod -> 'a1 coq_Sequence paths

val coq_SequenceAssembly :
  ('a1 coq_Sequence, (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod) weq

val coq_Sequence_rect :
  'a2 -> ('a1 coq_Sequence -> 'a1 -> 'a2 -> 'a2) -> 'a1 coq_Sequence -> 'a2

val coq_Sequence_rect_compute_nil :
  'a2 -> ('a1 coq_Sequence -> 'a1 -> 'a2 -> 'a2) -> 'a2 paths

val append_length : 'a1 coq_Sequence -> 'a1 -> nat paths

val concatenate : 'a1 coq_Sequence binop

val concatenate_length : 'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths

val concatenate_0 :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> 'a1 coq_Sequence paths

val concatenateStep :
  'a1 coq_Sequence -> nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths

val flatten : 'a1 coq_Sequence coq_Sequence -> 'a1 coq_Sequence

val flattenUnorderedSequence :
  'a1 coq_UnorderedSequence coq_UnorderedSequence -> 'a1 coq_UnorderedSequence

val flattenStep' :
  nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> (stn -> 'a1) paths

val flattenStep :
  'a1 coq_Sequence coq_NonemptySequence -> 'a1 coq_Sequence paths

val partition' :
  nat -> (stn -> nat) -> (stn -> 'a1) -> stn -> 'a1 coq_Sequence

val partition :
  nat -> (stn -> nat) -> (stn -> 'a1) -> 'a1 coq_Sequence coq_Sequence

val flatten_partition :
  nat -> (stn -> nat) -> (stn -> 'a1) -> (stn, 'a1) homot

val isassoc_concatenate :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> 'a1 coq_Sequence -> 'a1
  coq_Sequence paths

val reverse : 'a1 coq_Sequence -> 'a1 coq_Sequence

val reversereverse : 'a1 coq_Sequence -> 'a1 coq_Sequence paths

val reverse_index : 'a1 coq_Sequence -> stn -> 'a1 paths

val reverse_index' : 'a1 coq_Sequence -> stn -> 'a1 paths
