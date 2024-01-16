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

val kfinstruct_weqf : ('a1, 'a2) weq -> 'a1 kfinstruct -> 'a2 kfinstruct

val kfinstruct_weqb : ('a1, 'a2) weq -> 'a2 kfinstruct -> 'a1 kfinstruct

val kfinstruct_contr : 'a1 iscontr -> 'a1 kfinstruct

val kfinstruct_coprod :
  'a1 kfinstruct -> 'a2 kfinstruct -> ('a1, 'a2) coprod kfinstruct

val kfinstruct_dirprod :
  'a1 kfinstruct -> 'a2 kfinstruct -> ('a1, 'a2) dirprod kfinstruct

val kfinstruct_finstruct : 'a1 finstruct -> 'a1 kfinstruct

val kfinstruct_unit : coq_unit kfinstruct

val kfinstruct_bool : bool kfinstruct

val kfinstruct_stn : nat -> stn kfinstruct

val kfinstruct_stn_indexed :
  nat -> (stn -> 'a1 kfinstruct) -> (stn, 'a1) total2 kfinstruct

type 'x iskfinite = hProptoType

val kfinstruct_iskfinite : 'a1 kfinstruct -> 'a1 iskfinite

val iskfinite_weqf : ('a1, 'a2) weq -> 'a1 iskfinite -> 'a2 iskfinite

val iskfinite_weqb : ('a1, 'a2) weq -> 'a2 iskfinite -> 'a1 iskfinite

val iskfinite_from_surjection :
  ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> 'a1 iskfinite -> 'a2 iskfinite

val iskfinite_unit : coq_unit iskfinite

val iskfinite_bool : bool iskfinite

val iskfinite_contr : 'a1 iscontr -> 'a1 iskfinite

val iskfinite_coprod :
  'a1 iskfinite -> 'a2 iskfinite -> ('a1, 'a2) coprod iskfinite

val iskfinite_dirprod :
  'a1 iskfinite -> 'a2 iskfinite -> ('a1, 'a2) dirprod iskfinite

val iskfinite_isfinite : hProptoType -> 'a1 iskfinite
