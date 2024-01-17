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

