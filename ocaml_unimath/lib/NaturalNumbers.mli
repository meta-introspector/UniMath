open PartA
open PartB
open Preamble
open Propositions
open Sets

val negpaths0sx : nat -> nat paths neg

val negpathssx0 : nat -> nat paths neg

val invmaponpathsS : nat -> nat -> nat paths -> nat paths

val noeqinjS : nat -> nat -> nat paths neg -> nat paths neg

val natneq_iff_neq : nat -> nat -> (nat paths neg, hProptoType) logeq

val nat_nopath_to_neq : nat -> nat -> nat paths neg -> hProptoType

val isdeceqnat : nat isdeceq

val natgtb : nat -> nat -> bool

val natgthsnn : nat -> hProptoType

val natgthsn0 : nat -> hProptoType

val nat1gthtois0 : nat -> hProptoType -> nat paths

val istransnatgth :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isdecrelnatgth : nat isdecrel

val natlthnsn : nat -> hProptoType

val natlth1tois0 : nat -> hProptoType -> nat paths

val negnatgthtoleh : nat -> nat -> hProptoType neg -> hProptoType

val natleh0tois0 : nat -> hProptoType -> nat paths

val natleh0n : nat -> hProptoType

val istransnatleh :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isreflnatleh : nat -> hProptoType

val isantisymmnatleh : nat isantisymm

val natlthtoleh : nat -> nat -> hProptoType -> hProptoType

val natgehn0 : nat -> hProptoType

val istransnatgeh :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthorleh : nat -> nat -> (hProptoType, hProptoType) coprod

val natlthorgeh : nat -> nat -> (hProptoType, hProptoType) coprod

val natneqchoice :
  nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod

val natgehchoice :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgthgehtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlehlthtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthtogehsn : nat -> nat -> hProptoType -> hProptoType

val natlthtolehsn : nat -> nat -> hProptoType -> hProptoType

val natlthsntoleh : nat -> nat -> hProptoType -> hProptoType

val natplusr0 : nat -> nat paths

val natplusnsm : nat -> nat -> nat paths

val natpluscomm : nat -> nat -> nat paths

val natplusassoc : nat -> nat -> nat -> nat paths

val natgthandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehtolehs : nat -> nat -> hProptoType -> hProptoType

val natlehmplusnm : nat -> nat -> hProptoType

val plus_n_Sm : nat -> nat -> nat paths

val natlehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthp1toleh : nat -> nat -> hProptoType -> hProptoType

val natminuseqn : nat -> nat paths

val minusplusnmm : nat -> nat -> hProptoType -> nat paths
