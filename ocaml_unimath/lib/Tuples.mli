open NaturalNumbers
open PartA
open Preamble
open Propositions
open StandardFiniteSets
open UnivalenceAxiom

val stnweq : nat -> ((stn, coq_unit) coprod, stn) weq

val extend_tuple : nat -> (stn -> 'a1) -> 'a1 -> stn -> 'a1

val extend_tuple_dep :
  nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a2) -> 'a2 -> stn -> 'a2

val extend_tuple_dep_const :
  nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a2) -> 'a2 -> (stn -> 'a2) paths

val extend_tuple_i :
  nat -> (stn -> 'a1) -> 'a1 -> nat -> hProptoType -> hProptoType -> 'a1 paths

val extend_tuple_last :
  nat -> (stn -> 'a1) -> 'a1 -> stn -> nat paths -> 'a1 paths

val extend_tuple_inl : nat -> (stn -> 'a1) -> 'a1 -> stn -> 'a1 paths

val extend_tuple_inr : nat -> (stn -> 'a1) -> 'a1 -> 'a1 paths

val extend_tuple_eq :
  nat -> 'a1 -> (stn -> 'a1) -> (stn -> 'a1) -> (stn -> 'a1 paths) -> 'a1
  paths -> (stn -> 'a1) paths
