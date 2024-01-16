open NaturalNumbers
open PartA
open Preamble
open Propositions

type __ = Obj.t

val nat_dist : nat -> nat -> nat

module Discern :
 sig
  type nat_discern = __

  val helper_A : nat -> nat -> nat paths -> nat_discern

  val helper_B : nat -> nat -> nat_discern -> nat paths

  val nat_dist_anti : nat -> nat -> nat paths -> nat paths
 end

val nat_dist_symm : nat -> nat -> nat paths

val nat_dist_ge : nat -> nat -> hProptoType -> nat paths

val nat_dist_m0 : nat -> nat paths

val nat_dist_plus : nat -> nat -> nat paths

val nat_dist_le : nat -> nat -> hProptoType -> nat paths

val nat_dist_minus : nat -> nat -> hProptoType -> nat paths

val nat_dist_gt : nat -> nat -> hProptoType -> nat paths

val nat_dist_S : nat -> nat -> nat paths

val natleorle : nat -> nat -> (hProptoType, hProptoType) coprod

val nat_dist_trans : nat -> nat -> nat -> hProptoType

val natleplusminus : nat -> nat -> nat -> hProptoType -> hProptoType

val natltminus1 : nat -> nat -> hProptoType -> hProptoType

val natminusminusassoc : nat -> nat -> nat -> nat paths

val natminusplusltcomm :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType
