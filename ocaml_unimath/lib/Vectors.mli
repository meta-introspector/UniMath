open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions
open StandardFiniteSets
open UnivalenceAxiom

type __ = Obj.t

val stn_extens : nat -> stn -> stn -> nat paths -> stn paths

val fromstn0 : stn -> 'a1

type 'a vec = __

val vnil : 'a1 vec

val vcons : nat -> 'a1 -> 'a1 vec -> 'a1 vec

val drop : nat -> (stn -> 'a1) -> stn -> 'a1

val make_vec : nat -> (stn -> 'a1) -> 'a1 vec

val hd : nat -> 'a1 vec -> 'a1

val tl : nat -> 'a1 vec -> 'a1 vec

val el : nat -> 'a1 vec -> stn -> 'a1

val el_make_vec : nat -> (stn -> 'a1) -> (stn, 'a1) homot

val el_make_vec_fun : nat -> (stn -> 'a1) -> (stn -> 'a1) paths

val el_vcons_tl : nat -> 'a1 vec -> 'a1 -> stn -> 'a1 paths

val drop_el : nat -> 'a1 vec -> stn -> 'a1 paths

val el_tl : nat -> 'a1 vec -> stn -> 'a1 paths

val vec0_eq : 'a1 vec -> 'a1 vec -> 'a1 vec paths

val vecS_eq :
  nat -> 'a1 vec -> 'a1 vec -> 'a1 paths -> 'a1 vec paths -> 'a1 vec paths

val vec_extens :
  nat -> 'a1 vec -> 'a1 vec -> (stn -> 'a1 paths) -> 'a1 vec paths

val make_vec_el : nat -> 'a1 vec -> 'a1 vec paths

val isweqvecfun : nat -> ('a1 vec, stn -> 'a1) isweq

val weqvecfun : nat -> ('a1 vec, stn -> 'a1) weq
