open DecSet
open Lists
open Maybe
open NaturalNumbers
open PartA
open Preamble
open Propositions
open Sets
open Vectors

val head : 'a1 list -> 'a1 maybe

val tail : 'a1 list -> 'a1 list maybe

val list_head_cons : 'a1 -> 'a1 list -> 'a1 maybe paths

val list_tail_cons : 'a1 -> 'a1 list -> 'a1 list maybe paths

val cons_inj1 :
  'a1 -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths -> 'a1 paths

val cons_inj2 :
  'a1 -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths -> 'a1 list paths

val negpathsconsnil : 'a1 -> 'a1 list -> 'a1 list paths neg

val negpathsnilcons : 'a1 -> 'a1 list -> 'a1 list paths neg

val length_cons : 'a1 -> 'a1 list -> nat paths

val length_zero_back : 'a1 list -> nat paths -> 'a1 list paths

val length_one_back : 'a1 list -> nat paths -> ('a1, 'a1 list paths) total2

val length_concatenate : 'a1 list -> 'a1 list -> nat paths

val length_sublist1 : 'a1 list -> 'a1 list -> hProptoType

val length_sublist2 : 'a1 list -> 'a1 list -> hProptoType

val length_map : 'a1 list -> ('a1 -> 'a2) -> nat paths

val listset : hSet -> hSet

val fill : 'a1 -> nat -> 'a1 list

val map_const : 'a2 -> 'a1 list -> 'a2 list paths

val length_fill : 'a1 -> nat -> nat paths

val drop : 'a1 list -> nat -> 'a1 list

val drop_nil : nat -> 'a1 list paths

val drop_zero : 'a1 list -> 'a1 list paths

val drop_step : 'a1 -> 'a1 list -> nat -> 'a1 list paths

val drop_full : 'a1 list -> 'a1 list paths

val drop_concatenate :
  'a1 list -> 'a1 list -> nat -> hProptoType -> 'a1 list paths

val length_drop : 'a1 list -> nat -> nat paths

val prefix_remove :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe

val prefix_remove_stepeq :
  decSet -> pr1decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list
  maybe paths

val prefix_remove_stepneq :
  decSet -> pr1decSet -> pr1decSet -> pr1decSet paths neg -> pr1decSet list
  -> pr1decSet list -> pr1decSet list maybe paths

val prefix_remove_stepback :
  decSet -> pr1decSet -> pr1decSet -> pr1decSet list -> pr1decSet list ->
  pr1decSet list maybe paths neg -> pr1decSet paths

val prefix_remove_back :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> pr1decSet
  list maybe paths -> pr1decSet list paths

val prefix_remove_self :
  decSet -> pr1decSet list -> pr1decSet list maybe paths

type isprefix = pr1decSet list maybe paths neg

val isprefix_self : decSet -> pr1decSet list -> isprefix

val prefix_remove_concatenate :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> pr1decSet
  list -> pr1decSet list maybe paths -> pr1decSet list maybe paths

val prefix_remove_concatenate2 :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> hProptoType
  -> pr1decSet list maybe paths -> pr1decSet list maybe paths

val prefix_remove_prefix :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe paths

val prefix_remove_drop :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe paths
  neg -> pr1decSet list maybe paths
