open NaturalNumbers
open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets

type __ = Obj.t

type 'p negProp = (coq_UU, (__ isaprop, ('p neg, __) logeq) dirprod) total2

val negProp_to_isaprop : 'a1 negProp -> __ isaprop

val negProp_to_hProp : 'a1 negProp -> hProp

val negProp_to_iff : 'a1 negProp -> ('a1 neg, hProptoType) logeq

val negProp_to_neg : 'a1 negProp -> hProptoType -> 'a1 neg

val neg_to_negProp : 'a1 negProp -> 'a1 neg -> hProptoType

type ('x, 'p) negPred = 'x -> 'p negProp

type ('x, 'p) negReln = 'x -> 'x -> 'p negProp

type 'x neqProp = 'x paths negProp

type 'x neqPred = 'x -> 'x paths negProp

type 'x neqReln = 'x -> 'x -> 'x paths negProp

val negProp_to_complementary :
  'a1 negProp -> (('a1, hProptoType) coprod, ('a1, hProptoType)
  complementary) logeq

val negProp_to_uniqueChoice :
  'a1 negProp -> (('a1 isaprop, ('a1, hProptoType) coprod) dirprod, ('a1,
  hProptoType) coprod iscontr) logeq

type 'x isisolated_ne = 'x -> ('x paths, hProptoType) coprod

val isisolated_to_isisolated_ne :
  'a1 -> 'a1 neqPred -> 'a1 isisolated -> 'a1 isisolated_ne

val isisolated_ne_to_isisolated :
  'a1 -> 'a1 neqPred -> 'a1 isisolated_ne -> 'a1 isisolated

type 't isolated_ne = ('t, 't isisolated_ne) total2

val make_isolated_ne :
  'a1 -> 'a1 neqReln -> 'a1 isisolated_ne -> 'a1 isolated_ne

val pr1isolated_ne : 'a1 neqReln -> 'a1 isolated_ne -> 'a1

val isaproppathsfromisolated_ne :
  'a1 -> 'a1 neqPred -> 'a1 isisolated_ne -> 'a1 -> 'a1 paths isaprop

type 'x compl_ne = ('x, hProptoType) total2

val make_compl_ne : 'a1 -> 'a1 neqPred -> 'a1 -> hProptoType -> 'a1 compl_ne

val pr1compl_ne : 'a1 -> 'a1 neqPred -> 'a1 compl_ne -> 'a1

val make_negProp : 'a1 negProp

val make_neqProp : 'a1 -> 'a1 -> 'a1 neqProp

val isinclpr1compl_ne : 'a1 -> 'a1 neqPred -> ('a1 compl_ne, 'a1) isincl

val compl_ne_weq_compl : 'a1 -> 'a1 neqPred -> ('a1 compl, 'a1 compl_ne) weq

val compl_weq_compl_ne : 'a1 -> 'a1 neqPred -> ('a1 compl_ne, 'a1 compl) weq

val recompl_ne : 'a1 -> 'a1 neqPred -> ('a1 compl_ne, coq_unit) coprod -> 'a1

val maponcomplincl_ne :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 neqPred -> 'a2 neqPred ->
  'a1 compl_ne -> 'a2 compl_ne

val weqoncompl_ne :
  ('a1, 'a2) weq -> 'a1 -> 'a1 neqPred -> 'a2 neqPred -> ('a1 compl_ne, 'a2
  compl_ne) weq

val weqoncompl_ne_compute :
  ('a1, 'a2) weq -> 'a1 -> 'a1 neqPred -> 'a2 neqPred -> 'a1 compl_ne -> 'a2
  paths

val invrecompl_ne :
  'a1 -> 'a1 neqPred -> 'a1 isisolated -> 'a1 -> ('a1 compl_ne, coq_unit)
  coprod

val isweqrecompl_ne :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) isweq

val isweqrecompl_ne' :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) isweq

val weqrecompl_ne :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) weq

val isweqrecompl' :
  'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) isweq

val iscotrans_to_istrans_negReln :
  'a1 hrel -> ('a1, hProptoType) negReln -> 'a1 isdeccotrans -> 'a1 istrans

val natneq : nat -> nat -> nat paths negProp

type nat_compl = nat compl_ne

val weqdicompl : nat -> (nat, nat_compl) weq
