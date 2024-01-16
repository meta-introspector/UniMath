open NaturalNumbers
open PartA
open PartA0
open PartB
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t

type _UU2115_ = nat

module Uniqueness :
 sig
  val helper_A :
    'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1 paths, ('a1
    paths, nat -> 'a1 paths) dirprod) weq

  val helper_B :
    'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1) -> ((nat -> 'a1) paths, ('a1
    paths, nat -> 'a1 paths) dirprod) weq

  val helper_C :
    'a1 -> (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, (nat -> 'a1) paths) total2,
    (nat -> 'a1, ('a1 paths, nat -> 'a1 paths) dirprod) total2) weq

  val hNatRecursionUniq :
    'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1, ('a1 paths, nat -> 'a1 paths)
    dirprod) total2 iscontr

  val helper_D :
    'a1 -> (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, ('a1 paths, nat -> 'a1 paths)
    dirprod) total2, ((nat -> 'a1, nat -> 'a1 paths) total2, 'a1) hfiber) weq

  val hNatRecursion_weq :
    (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, nat -> 'a1 paths) total2, 'a1) weq
 end

val nat_dist : nat -> nat -> nat

module Discern :
 sig
  type nat_discern = __

  val coq_Unnamed_thm : nat -> nat -> nat_discern -> nat_discern

  val nat_discern_inj : nat -> nat -> nat_discern -> nat_discern

  val nat_discern_isaprop : nat -> nat -> nat_discern isaprop

  val nat_discern_unit : nat -> coq_UU paths

  val nat_discern_iscontr : nat -> nat_discern iscontr

  val helper_A : nat -> nat -> nat paths -> nat_discern

  val helper_B : nat -> nat -> nat_discern -> nat paths

  val coq_Unnamed_thm0 : nat -> nat -> nat_discern -> nat paths paths

  val helper_C : nat -> nat -> nat paths -> nat_discern

  val apSC : nat -> nat -> nat paths -> nat_discern paths

  val helper_D : nat -> nat -> (nat_discern, nat paths) isweq

  val coq_E : nat -> nat -> (nat_discern, nat paths) weq

  val nat_dist_anti : nat -> nat -> nat paths -> nat paths
 end

val nat_dist_symm : nat -> nat -> nat paths

val nat_dist_ge : nat -> nat -> hProptoType -> nat paths

val nat_dist_0m : nat -> nat paths

val nat_dist_m0 : nat -> nat paths

val nat_dist_plus : nat -> nat -> nat paths

val nat_dist_le : nat -> nat -> hProptoType -> nat paths

val nat_dist_minus : nat -> nat -> hProptoType -> nat paths

val nat_dist_gt : nat -> nat -> hProptoType -> nat paths

val nat_dist_S : nat -> nat -> nat paths

val natminuseqlr : nat -> nat -> nat -> hProptoType -> nat paths -> nat paths

val nat_dist_between_le :
  nat -> nat -> nat -> nat -> hProptoType -> nat paths -> (nat, (nat paths,
  nat paths) dirprod) total2

val nat_dist_between_ge :
  nat -> nat -> nat -> nat -> hProptoType -> nat paths -> (nat, (nat paths,
  nat paths) dirprod) total2

val nat_dist_between :
  nat -> nat -> nat -> nat -> nat paths -> (nat, (nat paths, nat paths)
  dirprod) total2

val natleorle : nat -> nat -> (hProptoType, hProptoType) coprod

val nat_dist_trans : nat -> nat -> nat -> hProptoType

val plusmn0n0 : nat -> nat -> nat paths -> nat paths

val plusmn0m0 : nat -> nat -> nat paths -> nat paths

val natminus0le : nat -> nat -> nat paths -> hProptoType

val minusxx : nat -> nat paths

val minusSxx : nat -> nat paths

val natminusminus : nat -> nat -> hProptoType -> nat paths

val natplusminus : nat -> nat -> nat -> nat paths -> nat paths

val natleplusminus : nat -> nat -> nat -> hProptoType -> hProptoType

val natltminus1 : nat -> nat -> hProptoType -> hProptoType

val natminusminusassoc : nat -> nat -> nat -> nat paths

val natminusplusltcomm :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val nat_le_diff :
  _UU2115_ -> _UU2115_ -> hProptoType -> (_UU2115_, nat paths) total2
