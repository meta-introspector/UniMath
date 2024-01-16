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

val stnset : nat -> hSet

val stn_to_nat : nat -> pr1hSet -> pr1hSet

val stnposet : nat -> coq_Poset

val lastelement : nat -> stn

val lastelement_ge : nat -> stn -> hProptoType

val firstelement : nat -> stn

val firstelement_le : nat -> stn -> hProptoType

val firstValue : nat -> (stn -> 'a1) -> 'a1

val lastValue : nat -> (stn -> 'a1) -> 'a1

val dualelement_0_empty : nat -> stn -> nat paths -> empty

val dualelement_lt : nat -> nat -> hProptoType -> hProptoType

val dualelement : nat -> stn -> stn

val stnmtostnn : nat -> nat -> hProptoType -> stn -> stn

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

val compute_pr1_dni_first : nat -> stn -> nat paths

val dni_last : nat -> stn -> nat paths

val dni_first : nat -> stn -> nat paths

val dni_firstelement : nat -> stn -> stn

val replace_dni_first : nat -> (stn -> stn) paths

val dni_lastelement : nat -> stn -> stn

val replace_dni_last : nat -> (stn -> stn) paths

val dni_lastelement_ord : nat -> stn -> stn -> hProptoType -> hProptoType

val pr1_dni_lastelement : nat -> stn -> nat paths

val dni_last_lt : nat -> stn -> hProptoType

val dnicommsq : nat -> stn -> (nat, stn, nat, stn) commsqstr

val dnihfsq : nat -> stn -> (nat, stn, nat, stn) hfsqstr

val dni_neq_i : nat -> stn -> stn -> hProptoType

val weqhfiberdnihfiberdi :
  nat -> stn -> stn -> ((stn, stn) hfiber, (nat, nat) hfiber) weq

val neghfiberdni : nat -> stn -> (stn, stn) hfiber neg

val iscontrhfiberdni :
  nat -> stn -> stn -> hProptoType -> (stn, stn) hfiber iscontr

val isdecincldni : nat -> stn -> (stn, stn) isdecincl

val isincldni : nat -> stn -> (stn, stn) isincl

val sni : nat -> stn -> stn -> stn

type stn_compl = stn compl_ne

val dnitocompl : nat -> stn -> stn -> stn_compl

val isweqdnitocompl : nat -> stn -> (stn, stn_compl) isweq

val weqdnicompl : nat -> stn -> (stn, stn_compl) weq

val weqdnicompl_compute : nat -> stn -> stn -> stn paths

val weqdnicoprod_provisional : nat -> stn -> ((stn, coq_unit) coprod, stn) weq

val weqdnicoprod_map : nat -> stn -> (stn, coq_unit) coprod -> stn

val weqdnicoprod_compute : nat -> stn -> ((stn, coq_unit) coprod, stn) homot

val weqdnicoprod : nat -> stn -> ((stn, coq_unit) coprod, stn) weq

val weqoverdnicoprod :
  nat -> ((stn, 'a1) total2, ((stn, 'a1) total2, 'a1) coprod) weq

val weqoverdnicoprod_eq1 : nat -> stn -> 'a1 -> (stn, 'a1) total2 paths

val weqoverdnicoprod_eq1' :
  nat -> (stn, 'a1) total2 -> (stn, 'a1) total2 paths

val weqoverdnicoprod_eq2 : nat -> 'a1 -> (stn, 'a1) total2 paths

val weqdnicoprod_invmap : nat -> stn -> stn -> (stn, coq_unit) coprod

val negstn0 : stn neg

val weqstn0toempty : (stn, empty) weq

val weqstn1tounit : (stn, coq_unit) weq

val iscontrstn1 : stn iscontr

val isconnectedstn1 : stn -> stn -> stn paths

val isinclfromstn1 : (stn -> 'a1) -> 'a1 isaset -> (stn, 'a1) isincl

val weqstn2tobool : (stn, bool) weq

val isinjstntonat : nat -> hProptoType

val weqfromcoprodofstn_invmap : nat -> nat -> stn -> (stn, stn) coprod

val weqfromcoprodofstn_invmap_r0 : nat -> stn -> (stn, stn) coprod paths

val weqfromcoprodofstn_map : nat -> nat -> (stn, stn) coprod -> stn

val weqfromcoprodofstn_eq1 :
  nat -> nat -> (stn, stn) coprod -> (stn, stn) coprod paths

val weqfromcoprodofstn_eq2 : nat -> nat -> stn -> stn paths

val weqfromcoprodofstn : nat -> nat -> ((stn, stn) coprod, stn) weq

val pr1_eqweqmap_stn : nat -> nat -> nat paths -> stn -> nat paths

val coprod_stn_assoc :
  nat -> nat -> nat -> (((stn, stn) coprod, stn) coprod, stn) homot

val stnsum : nat -> (stn -> nat) -> nat

val stnsum_step : nat -> (stn -> nat) -> nat paths

val stnsum_eq :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn, nat) homot -> nat paths

val transport_stnsum : nat -> nat -> nat paths -> (stn -> nat) -> nat paths

val stnsum_le :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType

val transport_stn : nat -> nat -> nat paths -> stn -> stn paths

val stnsum_left_right : nat -> nat -> (stn -> nat) -> nat paths

val stnsum_left_le : nat -> nat -> (stn -> nat) -> hProptoType

val stnsum_left_le' : nat -> nat -> (stn -> nat) -> hProptoType -> hProptoType

val stnsum_dni : nat -> (stn -> nat) -> stn -> nat paths

val stnsum_pos : nat -> (stn -> nat) -> stn -> hProptoType

val stnsum_pos_0 : nat -> (stn -> nat) -> hProptoType

val stnsum_1 : nat -> nat paths

val stnsum_const : nat -> nat -> nat paths

val stnsum_last_le : nat -> (stn -> nat) -> hProptoType

val stnsum_first_le : nat -> (stn -> nat) -> hProptoType

val _c_ : nat -> (stn -> nat) -> (stn, stn) total2 -> hProptoType

val weqstnsum_map : nat -> (stn -> nat) -> (stn, stn) total2 -> stn

val weqstnsum_invmap : nat -> (stn -> nat) -> stn -> (stn, stn) total2

val weqstnsum_invmap_step1 :
  nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths

val weqstnsum_invmap_step2 :
  nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths

val partial_sum_prop_aux :
  nat -> (stn -> nat) -> stn -> stn -> stn -> stn -> hProptoType ->
  hProptoType

val partial_sum_prop :
  nat -> (stn -> nat) -> nat -> (stn, (stn, nat paths) total2) total2 isaprop

val partial_sum_slot_subproof :
  nat -> (stn -> nat) -> nat -> stn -> stn -> nat paths -> nat paths

val partial_sum_slot :
  nat -> (stn -> nat) -> nat -> hProptoType -> (stn, (stn, nat paths) total2)
  total2 iscontr

val stn_right_first : nat -> nat -> stn paths

val nat_rect_step : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 paths

val weqstnsum1_prelim : nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val weqstnsum1_step :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq paths

val weqstnsum1_prelim_eq :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) homot

val weqstnsum1_prelim_eq' :
  nat -> (stn -> nat) -> (stn, (stn, stn) total2) homot

val weqstnsum1 : nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val weqstnsum1_eq : nat -> (stn -> nat) -> ((stn, stn) total2 -> stn) paths

val weqstnsum1_eq' : nat -> (stn -> nat) -> (stn -> (stn, stn) total2) paths

val weqstnsum :
  nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> ((stn, 'a1) total2, stn)
  weq

val weqstnsum2 :
  nat -> (stn -> nat) -> ('a1 -> stn) -> (stn -> (stn, ('a1, stn) hfiber)
  weq) -> ('a1, stn) weq

val lexicalEnumeration : nat -> (stn -> nat) -> (stn, (stn, stn) total2) weq

val inverse_lexicalEnumeration :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val foldleft : 'a1 -> 'a1 binop -> nat -> (stn -> 'a1) -> 'a1

val foldright : 'a1 binop -> 'a1 -> nat -> (stn -> 'a1) -> 'a1

val weqfromprodofstn : nat -> nat -> ((stn, stn) dirprod, stn) weq

val weqfromdecsubsetofstn :
  nat -> (stn -> bool) -> (nat, ((stn, bool) hfiber, stn) weq) total2

val weqfromhfiberfromstn :
  nat -> 'a1 -> 'a1 isisolated -> (stn -> 'a1) -> (nat, ((stn, 'a1) hfiber,
  stn) weq) total2

val weqfromfunstntostn : nat -> nat -> (stn -> stn, stn) weq

val stnprod : nat -> (stn -> nat) -> nat

val stnprod_step : nat -> (stn -> nat) -> nat paths

val stnprod_eq :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn, nat) homot -> nat paths

val weqstnprod :
  nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> (stn -> 'a1, stn) weq

val weqweqstnsn : nat -> ((stn, stn) weq, (stn, (stn, stn) weq) dirprod) weq

val weqfromweqstntostn : nat -> ((stn, stn) weq, stn) weq

val ischoicebasestn : nat -> hProptoType

val negweqstnsn0 : nat -> (stn, stn) weq neg

val negweqstn0sn : nat -> (stn, stn) weq neg

val weqcutforstn : nat -> nat -> (stn, stn) weq -> (stn, stn) weq

val weqtoeqstn : nat -> nat -> (stn, stn) weq -> nat paths

val eqtoweqstn_subproof : nat -> nat -> nat paths -> stn -> hProptoType

val eqtoweqstn_subproof0 : nat -> nat -> nat paths -> stn -> hProptoType

val eqtoweqstn_subproof1 : nat -> nat -> nat paths -> stn -> stn paths

val eqtoweqstn_subproof2 : nat -> nat -> nat paths -> stn -> stn paths

val eqtoweqstn : nat -> nat -> nat paths -> (stn, stn) weq

val stnsdnegweqtoeq : nat -> nat -> (stn, stn) weq dneg -> nat paths

val weqforallnatlehn0 :
  (nat -> hProp) -> (nat -> hProptoType -> hProptoType, hProptoType) weq

val weqforallnatlehnsn' :
  nat -> (nat -> hProp) -> (nat -> hProptoType -> hProptoType, (nat ->
  hProptoType -> hProptoType, hProptoType) dirprod) weq

val weqexistsnatlehn0 : (nat -> hProp) -> (hProptoType, hProptoType) weq

val weqexistsnatlehnsn' :
  nat -> (nat -> hProp) -> (hProptoType, hProptoType) weq

val isdecbexists : nat -> (nat -> 'a1 isdecprop) -> hProptoType isdecprop

val isdecbforall :
  nat -> (nat -> 'a1 isdecprop) -> (nat -> hProptoType -> 'a1) isdecprop

val negbforalldectototal2neg :
  nat -> (nat -> 'a1 isdecprop) -> (nat -> hProptoType -> 'a1) neg -> (nat,
  (hProptoType, 'a1 neg) dirprod) total2

type 'f natdecleast = (nat, ('f, nat -> 'f -> hProptoType) dirprod) total2

val isapropnatdecleast : (nat -> 'a1 isdecprop) -> 'a1 natdecleast isaprop

val accth : (nat -> 'a1 isdecprop) -> hProptoType -> 'a1 natdecleast

val dni_lastelement_is_inj : nat -> stn -> stn -> stn paths -> stn paths

val dni_lastelement_eq : nat -> stn -> hProptoType -> stn paths

val lastelement_eq : nat -> stn -> nat paths -> stn paths

val concatenate' : nat -> nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1

val concatenate'_r0 :
  nat -> (stn -> 'a1) -> (stn -> 'a1) -> (stn -> 'a1) paths

val concatenate'_r0' : nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1 paths

val flatten' : nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> stn -> 'a1

val stn_predicate : nat -> nat -> hProptoType -> hProptoType -> 'a1 -> 'a1

type two = stn

val two_rec : 'a1 -> 'a1 -> stn -> 'a1

val two_rec_dep : 'a1 -> 'a1 -> two -> 'a1

type three = stn

val three_rec : 'a1 -> 'a1 -> 'a1 -> stn -> 'a1

val three_rec_dep : 'a1 -> 'a1 -> 'a1 -> three -> 'a1

type is_stn_increasing = stn -> stn -> hProptoType -> hProptoType

type is_stn_strictly_increasing = stn -> stn -> hProptoType -> hProptoType

val is_strincr_impl_incr :
  nat -> (stn -> nat) -> is_stn_strictly_increasing -> is_stn_increasing

val is_incr_impl_strincr :
  nat -> (stn -> nat) -> (stn, nat) isincl -> is_stn_increasing ->
  is_stn_strictly_increasing

val stnsum_ge1 : nat -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType

val stnsum_add : nat -> (stn -> nat) -> (stn -> nat) -> nat paths

val stnsum_lt :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType

val stnsum_diffs : nat -> (stn -> nat) -> is_stn_increasing -> nat paths

val stn_ord_incl :
  nat -> (stn -> nat) -> is_stn_strictly_increasing -> hProptoType

val stn_ord_inj :
  nat -> (stn, stn) incl -> (stn -> stn -> hProptoType -> hProptoType) -> stn
  -> stn paths

val stn_ord_bij :
  nat -> (stn, stn) weq -> (stn -> stn -> hProptoType -> hProptoType) -> stn
  -> stn paths
