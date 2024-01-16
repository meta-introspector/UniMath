open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions

type __ = Obj.t

type 'p negProp = (coq_UU, (__ isaprop, ('p neg, __) logeq) dirprod) total2

val negProp_to_isaprop : 'a1 negProp -> __ isaprop

val negProp_to_hProp : 'a1 negProp -> hProp

val negProp_to_iff : 'a1 negProp -> ('a1 neg, hProptoType) logeq

val neg_to_negProp : 'a1 negProp -> 'a1 neg -> hProptoType

type 'x neqPred = 'x -> 'x paths negProp

type 'x neqReln = 'x -> 'x -> 'x paths negProp

type 'x compl_ne = ('x, hProptoType) total2

val make_compl_ne : 'a1 -> 'a1 neqPred -> 'a1 -> hProptoType -> 'a1 compl_ne

val pr1compl_ne : 'a1 -> 'a1 neqPred -> 'a1 compl_ne -> 'a1

val recompl_ne : 'a1 -> 'a1 neqPred -> ('a1 compl_ne, coq_unit) coprod -> 'a1

val invrecompl_ne :
  'a1 -> 'a1 neqPred -> 'a1 isisolated -> 'a1 -> ('a1 compl_ne, coq_unit)
  coprod

val isweqrecompl_ne :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) isweq

val weqrecompl_ne :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) weq

val natneq : nat -> nat -> nat paths negProp

type nat_compl = nat compl_ne

val weqdicompl : nat -> (nat, nat_compl) weq
