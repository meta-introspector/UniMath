open NaturalNumbers
open NegativePropositions
open PartA
open PartB
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

type stn = (nat, hProptoType) total2

val make_stn : nat -> nat -> hProptoType -> stn

val stntonat : nat -> stn -> nat

val stnlt : nat -> stn -> hProptoType

val isinclstntonat : nat -> (stn, nat) isincl

val stn_ne_iff_neq : nat -> stn -> stn -> (stn paths neg, hProptoType) logeq

val stnneq : nat -> stn neqReln

val isisolatedinstn : nat -> stn -> stn isisolated

val isdeceqstn : nat -> stn isdeceq

val lastelement : nat -> stn

val firstelement : nat -> stn

val lastValue : nat -> (stn -> 'a1) -> 'a1

val dualelement_0_empty : nat -> stn -> nat paths -> empty

val dualelement_lt : nat -> nat -> hProptoType -> hProptoType

val dualelement : nat -> stn -> stn

val stn_left : nat -> nat -> stn -> stn

val stn_right : nat -> nat -> stn -> stn

val stn_left_compute : nat -> nat -> stn -> nat paths

val stn_right_compute : nat -> nat -> stn -> nat paths

val stn_left_0 : nat -> stn -> nat paths -> stn paths

val stn_left' : nat -> nat -> hProptoType -> stn -> stn

val stn_left'' : nat -> nat -> hProptoType -> stn -> stn

val stn_left_compare : nat -> nat -> hProptoType -> (stn -> stn) paths

val dni : nat -> stn -> stn -> stn

val compute_pr1_dni_last : nat -> stn -> nat paths

val dni_last : nat -> stn -> nat paths

val dni_firstelement : nat -> stn -> stn

val dni_lastelement : nat -> stn -> stn

val replace_dni_last : nat -> (stn -> stn) paths

type stn_compl = stn compl_ne

val weqdnicompl : nat -> stn -> (stn, stn_compl) weq

val weqdnicoprod_provisional : nat -> stn -> ((stn, coq_unit) coprod, stn) weq

val weqdnicoprod_map : nat -> stn -> (stn, coq_unit) coprod -> stn

val weqdnicoprod_compute : nat -> stn -> ((stn, coq_unit) coprod, stn) homot

val weqdnicoprod : nat -> stn -> ((stn, coq_unit) coprod, stn) weq

val weqoverdnicoprod :
  nat -> ((stn, 'a1) total2, ((stn, 'a1) total2, 'a1) coprod) weq

val negstn0 : stn neg

val weqstn0toempty : (stn, empty) weq

val weqstn1tounit : (stn, coq_unit) weq

val isinjstntonat : nat -> hProptoType

val weqfromcoprodofstn_invmap : nat -> nat -> stn -> (stn, stn) coprod

val weqfromcoprodofstn_invmap_r0 : nat -> stn -> (stn, stn) coprod paths

val weqfromcoprodofstn_map : nat -> nat -> (stn, stn) coprod -> stn

val weqfromcoprodofstn_eq1 :
  nat -> nat -> (stn, stn) coprod -> (stn, stn) coprod paths

val weqfromcoprodofstn_eq2 : nat -> nat -> stn -> stn paths

val weqfromcoprodofstn : nat -> nat -> ((stn, stn) coprod, stn) weq

val stnsum : nat -> (stn -> nat) -> nat

val stnsum_step : nat -> (stn -> nat) -> nat paths

val stnsum_eq :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn, nat) homot -> nat paths

val transport_stnsum : nat -> nat -> nat paths -> (stn -> nat) -> nat paths

val stnsum_left_right : nat -> nat -> (stn -> nat) -> nat paths

val stnsum_left_le' : nat -> nat -> (stn -> nat) -> hProptoType -> hProptoType

val _c_ : nat -> (stn -> nat) -> (stn, stn) total2 -> hProptoType

val weqstnsum_map : nat -> (stn -> nat) -> (stn, stn) total2 -> stn

val weqstnsum_invmap : nat -> (stn -> nat) -> stn -> (stn, stn) total2

val weqstnsum_invmap_step1 :
  nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths

val weqstnsum_invmap_step2 :
  nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths

val weqstnsum1_prelim : nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val weqstnsum1_step :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq paths

val weqstnsum1_prelim_eq :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) homot

val weqstnsum1_prelim_eq' :
  nat -> (stn -> nat) -> (stn, (stn, stn) total2) homot

val weqstnsum1 : nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val weqstnsum1_eq' : nat -> (stn -> nat) -> (stn -> (stn, stn) total2) paths

val weqstnsum :
  nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> ((stn, 'a1) total2, stn)
  weq

val inverse_lexicalEnumeration :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val ischoicebasestn : nat -> hProptoType

val concatenate' : nat -> nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1

val flatten' : nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> stn -> 'a1
