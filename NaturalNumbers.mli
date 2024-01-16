open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets

val natnegpaths : nat -> nat -> hProp

val natneq_hProp : nat -> nat -> hProp

val negpaths0sx : nat -> nat paths neg

val negpathssx0 : nat -> nat paths neg

val invmaponpathsS : nat -> nat -> nat paths -> nat paths

val noeqinjS : nat -> nat -> nat paths neg -> nat paths neg

val natneq_iff_neq : nat -> nat -> (nat paths neg, hProptoType) logeq

val nat_neq_to_nopath : nat -> nat -> hProptoType -> nat paths neg

val nat_nopath_to_neq : nat -> nat -> nat paths neg -> hProptoType

val natneq0sx : nat -> hProptoType

val natneqsx0 : nat -> hProptoType

val natneqinjS : nat -> nat -> hProptoType -> hProptoType

val isirrefl_natneq : nat -> hProptoType neg

val issymm_natneq : nat -> nat -> hProptoType -> hProptoType

val isdeceqnat : nat isdeceq

val isisolatedn : nat -> nat isisolated

val isasetnat : nat isaset

val natset : hSet

val nat_eq_or_neq : nat -> nat -> (nat paths, hProptoType) coprod

val isdecrel_natneq : nat isdecrel

val nateq : nat -> nat -> hProp

val isdecrelnateq : nat isdecrel

val natdeceq : nat decrel

val natdecneq : nat decrel

val natboolneq : nat brel

val isinclS : (nat, nat) isincl

val isdecinclS : (nat, nat) isdecincl

val natgtb : nat -> nat -> bool

val natgth : nat -> nat -> hProp

val negnatgth0n : nat -> hProptoType neg

val natgthsnn : nat -> hProptoType

val natgthsn0 : nat -> hProptoType

val negnatgth0tois0 : nat -> hProptoType neg -> nat paths

val natneq0togth0 : nat -> hProptoType -> hProptoType

val nat1gthtois0 : nat -> hProptoType -> nat paths

val istransnatgth :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isirreflnatgth : nat -> hProptoType neg

val natgthtoneq : nat -> nat -> hProptoType -> hProptoType

val isasymmnatgth : nat -> nat -> hProptoType -> hProptoType -> empty

val isantisymmnegnatgth :
  nat -> nat -> hProptoType neg -> hProptoType neg -> nat paths

val isdecrelnatgth : nat isdecrel

val natgthdec : nat decrel

val isnegrelnatgth : nat isnegrel

val iscoantisymmnatgth :
  nat -> nat -> hProptoType neg -> (hProptoType, nat paths) coprod

val iscotransnatgth :
  nat -> nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod

val natlth : nat -> nat -> hProp

val negnatlthn0 : nat -> hProptoType neg

val natlthnsn : nat -> hProptoType

val negnat0lthtois0 : nat -> hProptoType neg -> nat paths

val natneq0to0lth : nat -> hProptoType -> hProptoType

val natlth1tois0 : nat -> hProptoType -> nat paths

val istransnatlth :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isirreflnatlth : nat -> hProptoType neg

val natlthtoneq : nat -> nat -> hProptoType -> hProptoType

val isasymmnatlth : nat -> nat -> hProptoType -> hProptoType -> empty

val isantisymmnegnattth :
  nat -> nat -> hProptoType neg -> hProptoType neg -> nat paths

val isdecrelnatlth : nat isdecrel

val natlthdec : nat decrel

val isnegrelnatlth : nat isnegrel

val iscoantisymmnatlth :
  nat -> nat -> hProptoType neg -> (hProptoType, nat paths) coprod

val iscotransnatlth :
  nat -> nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod

val natleh : nat -> nat -> hProp

val isdecrelnatleh : nat isdecrel

val negnatlehsn0 : nat -> hProptoType neg

val natlehneggth : nat -> nat -> hProptoType -> hProptoType neg

val natgthnegleh : nat -> nat -> hProptoType -> hProptoType neg

val negnatSleh : nat -> hProptoType neg

val negnatgthtoleh : nat -> nat -> hProptoType neg -> hProptoType

val negnatlehtogth : nat -> nat -> hProptoType neg -> hProptoType

val neggth_logeq_leh : nat -> nat -> (hProptoType neg, hProptoType) logeq

val natleh0tois0 : nat -> hProptoType -> nat paths

val natleh0n : nat -> hProptoType

val negnatlehsnn : nat -> hProptoType neg

val istransnatleh :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isreflnatleh : nat -> hProptoType

val isantisymmnatleh : nat isantisymm

val natlehdec : nat decrel

val isnegrelnatleh : nat isnegrel

val natlthtoleh : nat -> nat -> hProptoType -> hProptoType

val iscoasymmnatleh : nat -> nat -> hProptoType neg -> hProptoType

val istotalnatleh : nat istotal

val natgeh : nat -> nat -> hProp

val nat0gehtois0 : nat -> hProptoType -> nat paths

val natgehn0 : nat -> hProptoType

val negnatgeh0sn : nat -> hProptoType neg

val negnatgehnsn : nat -> hProptoType neg

val istransnatgeh :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isreflnatgeh : nat -> hProptoType

val isantisymmnatgeh : nat -> nat -> hProptoType -> hProptoType -> nat paths

val isdecrelnatgeh : nat isdecrel

val natgehdec : nat decrel

val isnegrelnatgeh : nat isnegrel

val iscoasymmnatgeh : nat -> nat -> hProptoType neg -> hProptoType

val istotalnatgeh : nat istotal

val natgthtogeh : nat -> nat -> hProptoType -> hProptoType

val natlehtonegnatgth : nat -> nat -> hProptoType -> hProptoType neg

val natgthtonegnatleh : nat -> nat -> hProptoType -> hProptoType neg

val natgehtonegnatlth : nat -> nat -> hProptoType -> hProptoType neg

val natlthtonegnatgeh : nat -> nat -> hProptoType -> hProptoType neg

val negnatgehtolth : nat -> nat -> hProptoType neg -> hProptoType

val negnatlthtogeh : nat -> nat -> hProptoType neg -> hProptoType

val natlehnsn : nat -> hProptoType

val natgehsnn : nat -> hProptoType

val natgthorleh : nat -> nat -> (hProptoType, hProptoType) coprod

val natlthorgeh : nat -> nat -> (hProptoType, hProptoType) coprod

val natchoice0 : nat -> (nat paths, hProptoType) coprod

val natneqchoice :
  nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod

val natlehchoice :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgehchoice :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgthgehtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgehgthtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthlehtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlehlthtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natltltSlt :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthtogehsn : nat -> nat -> hProptoType -> hProptoType

val natgthsntogeh : nat -> nat -> hProptoType -> hProptoType

val natgehtogthsn : nat -> nat -> hProptoType -> hProptoType

val natgehsntogth : nat -> nat -> hProptoType -> hProptoType

val natlthtolehsn : nat -> nat -> hProptoType -> hProptoType

val natlehsntolth : nat -> nat -> hProptoType -> hProptoType

val natlehtolthsn : nat -> nat -> hProptoType -> hProptoType

val natlthsntoleh : nat -> nat -> hProptoType -> hProptoType

val natlehchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgehchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgthchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natlthchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natplusl0 : nat -> nat paths

val natplusr0 : nat -> nat paths

val natplusnsm : nat -> nat -> nat paths

val natpluscomm : nat -> nat -> nat paths

val natplusassoc : nat -> nat -> nat -> nat paths

val natgthtogths : nat -> nat -> hProptoType -> hProptoType

val negnatgthmplusnm : nat -> nat -> hProptoType neg

val negnatgthnplusnm : nat -> nat -> hProptoType neg

val natgthandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusm : nat -> nat -> hProptoType -> hProptoType

val natlthtolths : nat -> nat -> hProptoType -> hProptoType

val negnatlthplusnmm : nat -> nat -> hProptoType neg

val negnatlthplusnmn : nat -> nat -> hProptoType neg

val natlthandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandplusm : nat -> nat -> hProptoType -> hProptoType

val natlehtolehs : nat -> nat -> hProptoType -> hProptoType

val natlehmplusnm : nat -> nat -> hProptoType

val plus_n_Sm : nat -> nat -> nat paths

val natlehnplusnm : nat -> nat -> hProptoType

val natlehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplus :
  nat -> nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlehandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehtogehs : nat -> nat -> hProptoType -> hProptoType

val natgehplusnmm : nat -> nat -> hProptoType

val natgehplusnmn : nat -> nat -> hProptoType

val natgehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthtogthp1 : nat -> nat -> hProptoType -> hProptoType

val natlthtolthp1 : nat -> nat -> hProptoType -> hProptoType

val natlehtolehp1 : nat -> nat -> hProptoType -> hProptoType

val natgehtogehp1 : nat -> nat -> hProptoType -> hProptoType

val natgthtogehp1 : nat -> nat -> hProptoType -> hProptoType

val natgthp1togeh : nat -> nat -> hProptoType -> hProptoType

val natlehp1tolth : nat -> nat -> hProptoType -> hProptoType

val natlthtolehp1 : nat -> nat -> hProptoType -> hProptoType

val natlthp1toleh : nat -> nat -> hProptoType -> hProptoType

val natgehp1togth : nat -> nat -> hProptoType -> hProptoType

val natlehchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgehchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgthchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natlthchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natlehchoice4 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val pathsitertoplus : nat -> nat -> nat paths

val isinclnatplusr : nat -> (nat, nat) isincl

val isinclnatplusl : nat -> (nat, nat) isincl

val natplusrcan : nat -> nat -> nat -> nat paths -> nat paths

val natpluslcan : nat -> nat -> nat -> nat paths -> nat paths

val iscontrhfibernatplusr :
  nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr

val iscontrhfibernatplusl :
  nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr

val neghfibernatplusr : nat -> nat -> hProptoType -> (nat, nat) hfiber neg

val isdecinclnatplusr : nat -> (nat, nat) isdecincl

val minuseq0 : nat -> nat -> hProptoType -> nat paths

val minuseq0' : nat -> nat paths

val minusgth0 : nat -> nat -> hProptoType -> hProptoType

val minusgth0inv : nat -> nat -> hProptoType -> hProptoType

val natminuseqn : nat -> nat paths

val natminuslehn : nat -> nat -> hProptoType

val natminusgehn : nat -> nat -> hProptoType

val natminuslthn : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natminuslthninv : nat -> nat -> hProptoType -> hProptoType

val minusplusnmm : nat -> nat -> hProptoType -> nat paths

val minusplusnmmineq : nat -> nat -> hProptoType

val plusminusnmm : nat -> nat -> nat paths

val minusminusmmn : nat -> nat -> hProptoType -> nat paths

val natgthtogthm1 : nat -> nat -> hProptoType -> hProptoType

val natlthtolthm1 : nat -> nat -> hProptoType -> hProptoType

val natlehtolehm1 : nat -> nat -> hProptoType -> hProptoType

val natgehtogehm1 : nat -> nat -> hProptoType -> hProptoType

val natgthtogehm1 : nat -> nat -> hProptoType -> hProptoType

val natgehandminusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandminusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandminusrinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthandminusl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natmult0n : nat -> nat paths

val natmultn0 : nat -> nat paths

val multsnm : nat -> nat -> nat paths

val multnsm : nat -> nat -> nat paths

val natmultcomm : nat -> nat -> nat paths

val natrdistr : nat -> nat -> nat -> nat paths

val natldistr : nat -> nat -> nat -> nat paths

val natmultassoc : nat -> nat -> nat -> nat paths

val natmultl1 : nat -> nat paths

val natmultr1 : nat -> nat paths

val natplusnonzero : nat -> nat -> hProptoType -> hProptoType

val natneq0andmult : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natneq0andmultlinv : nat -> nat -> hProptoType -> hProptoType

val natneq0andmultrinv : nat -> nat -> hProptoType -> hProptoType

val natgthandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthandmultlinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandmultrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthandmultlinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandmultrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandmultl : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandmultr : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandmultlinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlehandmultrinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgehandmultl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandmultr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandmultlinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgehandmultrinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natdivrem : nat -> nat -> (nat, nat) dirprod

val natdiv : nat -> nat -> nat

val natrem : nat -> nat -> nat

val lthnatrem : nat -> nat -> hProptoType -> hProptoType

val natdivremrule : nat -> nat -> hProptoType -> nat paths

val natlehmultnatdiv : nat -> nat -> hProptoType -> hProptoType

val natdivremunique :
  nat -> nat -> nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths
  -> (nat paths, nat paths) dirprod

val natdivremandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> (nat paths, nat paths)
  dirprod

val natdivandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natremandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natdivremandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> (nat paths, nat paths)
  dirprod

val natdivandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natremandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natpower : nat -> nat -> nat

val factorial : nat -> nat

val di : nat -> nat -> nat

val di_eq1 : nat -> nat -> hProptoType -> nat paths

val di_eq2 : nat -> nat -> hProptoType -> nat paths

val di_neq_i : nat -> nat -> hProptoType

val natlehdinsn : nat -> nat -> hProptoType

val natgehdinn : nat -> nat -> hProptoType

val isincldi : nat -> (nat, nat) isincl

val neghfiberdi : nat -> (nat, nat) hfiber neg

val iscontrhfiberdi : nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr

val isdecincldi : nat -> (nat, nat) isdecincl

val si : nat -> nat -> nat

val natleh_neq : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natminusminus : nat -> nat -> nat -> nat paths

val natltplusS : nat -> nat -> hProptoType

val nat_split : nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natplusminusle : nat -> nat -> nat -> hProptoType -> nat paths

val natdiffplusdiff :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths
