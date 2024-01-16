open FiniteSets
open PartA
open PartA0
open Preamble
open Propositions
open StandardFiniteSets

type 'x kfinstruct = (nat, (stn -> 'x, (stn, 'x) issurjective) total2) total2

val make_kfinstruct :
  nat -> (stn -> 'a1) -> (stn, 'a1) issurjective -> 'a1 kfinstruct

val kfinstruct_cardinality : 'a1 kfinstruct -> nat

val kfinstruct_map : 'a1 kfinstruct -> stn -> 'a1

val issurjective_kfinstruct : 'a1 kfinstruct -> (stn, 'a1) issurjective

val kfinstruct_from_surjection :
  ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> 'a1 kfinstruct -> 'a2 kfinstruct

val kfinstruct_weqb : ('a1, 'a2) weq -> 'a2 kfinstruct -> 'a1 kfinstruct

val kfinstruct_finstruct : 'a1 finstruct -> 'a1 kfinstruct

val kfinstruct_stn : nat -> stn kfinstruct

val kfinstruct_stn_indexed :
  nat -> (stn -> 'a1 kfinstruct) -> (stn, 'a1) total2 kfinstruct

type 'x iskfinite = hProptoType

val kfinstruct_iskfinite : 'a1 kfinstruct -> 'a1 iskfinite
