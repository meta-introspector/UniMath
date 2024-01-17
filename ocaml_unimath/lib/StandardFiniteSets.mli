open DecidablePropositions
open NaturalNumbers
open NegativePropositions
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

type stn = (nat, hProptoType) total2

val make_stn : nat -> nat -> hProptoType -> stn

val stntonat : nat -> stn -> nat

val stnlt : nat -> stn -> hProptoType

val stn_eq : nat -> stn -> stn -> nat paths -> stn paths

val isinclstntonat : nat -> (stn, nat) isincl

val stntonat_incl : nat -> (stn, nat) incl

val isdecinclstntonat : nat -> (stn, nat) isdecincl

val neghfiberstntonat : nat -> nat -> hProptoType -> (stn, nat) hfiber neg

val iscontrhfiberstntonat :
  nat -> nat -> hProptoType -> (stn, nat) hfiber iscontr

val stn_ne_iff_neq : nat -> stn -> stn -> (stn paths neg, hProptoType) logeq

val stnneq : nat -> stn neqReln

val isisolatedinstn : nat -> stn -> stn isisolated

val stnneq_iff_nopath :
  nat -> stn -> stn -> (stn paths neg, hProptoType) logeq

val stnneq_to_nopath : nat -> stn -> stn -> hProptoType -> stn paths neg

val isdeceqstn : nat -> stn isdeceq

val stn_eq_or_neq : nat -> stn -> stn -> (stn paths, hProptoType) coprod

val weqisolatedstntostn : nat -> (stn isolated, stn) weq

val isasetstn : nat -> stn isaset

