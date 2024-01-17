open PartA
open PartB
open PartC
open Preamble
open UnivalenceAxiom

val totaltoforall :
  ('a1 -> 'a2, 'a1 -> 'a3) total2 -> 'a1 -> ('a2, 'a3) total2

val foralltototal :
  ('a1 -> ('a2, 'a3) total2) -> ('a1 -> 'a2, 'a1 -> 'a3) total2

val isweqforalltototal :
  ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) isweq

val isweqtotaltoforall :
  (('a1 -> 'a2, 'a1 -> 'a3) total2, 'a1 -> ('a2, 'a3) total2) isweq

(* val weqforalltototal : *)
(*   ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq *)

(* val weqtotaltoforall : *)
(*   (('a1 -> 'a2, 'a1 -> 'a3) total2, 'a1 -> ('a2, 'a3) total2) weq *)

(* val weqfuntototaltototal : *)
(*   ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq *)

val funtoprodtoprod :
  ('a1 -> ('a2, 'a3) dirprod) -> ('a1 -> 'a2, 'a1 -> 'a3) dirprod

val prodtofuntoprod :
  ('a1 -> 'a2, 'a1 -> 'a3) dirprod -> 'a1 -> ('a2, 'a3) dirprod

(* val weqfuntoprodtoprod : *)
(*   ('a1 -> ('a2, 'a3) dirprod, ('a1 -> 'a2, 'a1 -> 'a3) dirprod) weq *)

val maponsec : ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

val maponsec1 : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

val hfibertoforall :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a2, 'a1 -> 'a3) hfiber ->
  'a1 -> ('a2, 'a3) hfiber

val foralltohfiber :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber) -> ('a1
  -> 'a2, 'a1 -> 'a3) hfiber

val isweqhfibertoforall :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> (('a1 -> 'a2, 'a1 -> 'a3) hfiber,
  'a1 -> ('a2, 'a3) hfiber) isweq

val weqhfibertoforall :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> (('a1 -> 'a2, 'a1 -> 'a3) hfiber,
  'a1 -> ('a2, 'a3) hfiber) weq

val isweqforalltohfiber :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber, ('a1 ->
  'a2, 'a1 -> 'a3) hfiber) isweq

val weqforalltohfiber :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber, ('a1 ->
  'a2, 'a1 -> 'a3) hfiber) weq

val isweqmaponsec : ('a1 -> ('a2, 'a3) weq) -> ('a1 -> 'a2, 'a1 -> 'a3) isweq

val weqonsecfibers : ('a1 -> ('a2, 'a3) weq) -> ('a1 -> 'a2, 'a1 -> 'a3) weq

val weqffun : ('a2, 'a3) weq -> ('a1 -> 'a2, 'a1 -> 'a3) weq

val maponsec1l0 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1 -> 'a2) -> 'a1 -> 'a2

val maponsec1l1 : 'a1 -> ('a1 -> 'a2) -> 'a2 paths

val maponsec1l2 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths

val isweqmaponsec1 : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq

val weqonsecbase : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) weq

val weqbfun : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) weq

val iscontrsecoverempty : (empty -> 'a1) iscontr

val iscontrsecoverempty2 : 'a1 neg -> ('a1 -> 'a2) iscontr

val secovercoprodtoprod :
  (('a1, 'a2) coprod -> 'a3) -> ('a1 -> 'a3, 'a2 -> 'a3) dirprod

val prodtosecovercoprod :
  ('a1 -> 'a3, 'a2 -> 'a3) dirprod -> ('a1, 'a2) coprod -> 'a3

(* val weqsecovercoprodtoprod : *)
(*   (('a1, 'a2) coprod -> 'a3, ('a1 -> 'a3, 'a2 -> 'a3) dirprod) weq *)

val iscontrfunfromempty : (empty -> 'a1) iscontr

val iscontrfunfromempty2 : 'a2 neg -> ('a2 -> 'a1) iscontr

val funfromcoprodtoprod :
  (('a1, 'a2) coprod -> 'a3) -> ('a1 -> 'a3, 'a2 -> 'a3) dirprod

val prodtofunfromcoprod :
  ('a1 -> 'a3, 'a2 -> 'a3) dirprod -> ('a1, 'a2) coprod -> 'a3

(* val weqfunfromcoprodtoprod : *)
(*   (('a1, 'a2) coprod -> 'a3, ('a1 -> 'a3, 'a2 -> 'a3) dirprod) weq *)

val tosecoverunit : 'a1 -> coq_unit -> 'a1

(* val weqsecoverunit : (coq_unit -> 'a1, 'a1) weq *)

(* val weqsecovercontr : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq *)

val tosecovertotal2 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

(* val weqsecovertotal2 : (('a1, 'a2) total2 -> 'a3, 'a1 -> 'a2 -> 'a3) weq *)

(* val weqfunfromunit : (coq_unit -> 'a1, 'a1) weq *)

(* val weqfunfromcontr : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq *)

(* val weqfunfromtotal2 : (('a1, 'a2) total2 -> 'a3, 'a1 -> 'a2 -> 'a3) weq *)

(* val weqfunfromdirprod : (('a1, 'a2) dirprod -> 'a3, 'a1 -> 'a2 -> 'a3) weq *)

val impred : nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel

val impred_iscontr : ('a1 -> 'a2 iscontr) -> ('a1 -> 'a2) iscontr

val impred_isaprop : ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2) isaprop

val impred_isaset : ('a1 -> 'a2 isaset) -> ('a1 -> 'a2) isaset

val impredtwice :
  nat -> ('a1 -> 'a2 -> 'a3 isofhlevel) -> ('a1 -> 'a2 -> 'a3) isofhlevel

val impredfun : nat -> 'a2 isofhlevel -> ('a1 -> 'a2) isofhlevel

val impredtech1 : nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel

val iscontrfuntounit : ('a1 -> coq_unit) iscontr

val iscontrfuntocontr : 'a2 iscontr -> ('a1 -> 'a2) iscontr

val isapropimpl : 'a2 isaprop -> ('a1 -> 'a2) isaprop

val isapropneg2 : 'a2 neg -> ('a1 -> 'a2) isaprop

val iscontriscontr : 'a1 iscontr -> 'a1 iscontr iscontr

val isapropiscontr : 'a1 iscontr isaprop

val isapropisweq : ('a1 -> 'a2) -> ('a1, 'a2) isweq isaprop

val isapropisisolated : 'a1 -> 'a1 isisolated isaprop

val isapropisdeceq : 'a1 isdeceq isaprop

val isapropisofhlevel : nat -> 'a1 isofhlevel isaprop

val isapropisaprop : 'a1 isaprop isaprop

val isapropisdecprop : 'a1 isdecprop isaprop

val isapropisaset : 'a1 isaset isaprop

val isapropisofhlevelf : nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf isaprop

val isapropisincl : ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf isaprop

val isaprop_isInjective : ('a1 -> 'a2) -> ('a1, 'a2) isInjective isaprop

val incl_injectivity :
  ('a1 -> 'a2) -> (('a1, 'a2) isincl, ('a1, 'a2) isInjective) weq

val isinclpr1weq : (('a1, 'a2) weq, 'a1 -> 'a2) isincl

val isinjpr1weq : (('a1, 'a2) weq, 'a1 -> 'a2) isInjective

val isinclpr1isolated : ('a1 isolated, 'a1) isincl

val weqcomp_assoc :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a4) weq -> ('a1, 'a4) weq paths

val eqweqmap_pathscomp0 : coq_UU paths -> coq_UU paths -> ('a1, 'a3) weq paths

(* val inv_idweq_is_idweq : ('a1, 'a1) weq paths *)

val eqweqmap_pathsinv0 : coq_UU paths -> ('a2, 'a1) weq paths

val weqfweq : ('a2, 'a3) weq -> (('a1, 'a2) weq, ('a1, 'a3) weq) weq

val weqbweq : ('a1, 'a2) weq -> (('a2, 'a3) weq, ('a1, 'a3) weq) weq

val weqweq : ('a1, 'a2) weq -> (('a1, 'a1) weq, ('a2, 'a2) weq) weq

(* val weqinvweq : (('a1, 'a2) weq, ('a2, 'a1) weq) weq *)

val isofhlevelsnweqtohlevelsn :
  nat -> 'a2 isofhlevel -> ('a1, 'a2) weq isofhlevel

val isofhlevelsnweqfromhlevelsn :
  nat -> 'a2 isofhlevel -> ('a2, 'a1) weq isofhlevel

val isapropweqtocontr : 'a2 iscontr -> ('a1, 'a2) weq isaprop

val isapropweqfromcontr : 'a2 iscontr -> ('a2, 'a1) weq isaprop

val isapropweqtoprop : 'a2 isaprop -> ('a1, 'a2) weq isaprop

val isapropweqfromprop : 'a2 isaprop -> ('a2, 'a1) weq isaprop

val isasetweqtoset : 'a2 isaset -> ('a1, 'a2) weq isaset

val isasetweqfromset : 'a2 isaset -> ('a2, 'a1) weq isaset

val isapropweqtoempty : ('a1, empty) weq isaprop

val isapropweqtoempty2 : 'a2 neg -> ('a1, 'a2) weq isaprop

val isapropweqfromempty : (empty, 'a1) weq isaprop

val isapropweqfromempty2 : 'a2 neg -> ('a2, 'a1) weq isaprop

val isapropweqtounit : ('a1, coq_unit) weq isaprop

val isapropweqfromunit : (coq_unit, 'a1) weq isaprop

val cutonweq :
  'a1 -> 'a1 isisolated -> ('a1, 'a1) weq -> ('a1 isolated, ('a1 compl, 'a1
  compl) weq) dirprod

val invcutonweq :
  'a1 -> 'a1 isisolated -> ('a1 isolated, ('a1 compl, 'a1 compl) weq) dirprod
  -> ('a1, 'a1) weq

val pathsinvcuntonweqoft :
  'a1 -> 'a1 isisolated -> ('a1 isolated, ('a1 compl, 'a1 compl) weq) dirprod
  -> 'a1 paths

val weqcutonweq :
  'a1 -> 'a1 isisolated -> (('a1, 'a1) weq, ('a1 isolated, ('a1 compl, 'a1
  compl) weq) dirprod) weq

val weqcompidl : ('a1, 'a2) weq -> ('a1, 'a2) weq paths

val weqcompidr : ('a1, 'a2) weq -> ('a1, 'a2) weq paths

val weqcompinvl : ('a1, 'a2) weq -> ('a2, 'a2) weq paths

val weqcompinvr : ('a1, 'a2) weq -> ('a1, 'a1) weq paths

val weqcompassoc :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a4) weq -> ('a1, 'a4) weq paths

val weqcompweql : ('a1, 'a2) weq -> (('a2, 'a3) weq, ('a1, 'a3) weq) isweq

val weqcompweqr : ('a2, 'a3) weq -> (('a1, 'a2) weq, ('a1, 'a3) weq) isweq

val weqcompinjr :
  ('a1, 'a2) weq -> ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq paths
  -> ('a1, 'a2) weq paths

val weqcompinjl :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq paths
  -> ('a2, 'a3) weq paths

val invweqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a1) weq paths

val invmapweqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3 -> 'a1) paths
