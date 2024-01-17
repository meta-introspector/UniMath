open PartA
open PartB
open Preamble
open UnivalenceAxiom

val isapropneg : 'a1 neg isaprop

val isaprop_isProofIrrelevant : 'a1 isProofIrrelevant isaprop

val isapropdneg : 'a1 dneg isaprop

type 'x isaninvprop = ('x, 'x dneg) isweq

val invimpl : 'a1 isaninvprop -> 'a1 dneg -> 'a1

val isapropaninvprop : 'a1 isaninvprop -> 'a1 isaprop

val isaninvpropneg : 'a1 neg isaninvprop

val isapropdec : 'a1 isaprop -> 'a1 decidable isaprop

type 'x compl = ('x, 'x paths neg) total2

val make_compl : 'a1 -> 'a1 -> 'a1 paths neg -> ('a1, 'a1 paths neg) total2

val pr1compl : 'a1 -> ('a1, 'a1 paths neg) total2 -> 'a1

val isinclpr1compl : 'a1 -> (('a1, 'a1 paths neg) total2, 'a1) isincl

val recompl : 'a1 -> ('a1 compl, coq_unit) coprod -> 'a1

val maponcomplincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 compl -> 'a2 compl

val weqoncompl : ('a1, 'a2) weq -> 'a1 -> ('a1 compl, 'a2 compl) weq

val weqoncompl_compute : ('a1, 'a2) weq -> 'a1 -> 'a1 compl -> 'a2 paths

val homotweqoncomplcomp :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> 'a1 -> ('a1 compl, 'a3 compl) homot

val invrecompl : 'a1 -> 'a1 isisolated -> 'a1 -> ('a1 compl, coq_unit) coprod

val isweqrecompl :
  'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) isweq

val weqrecompl :
  'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) weq

val homotrecomplnat :
  ('a1, 'a2) weq -> 'a1 -> ('a1 compl, coq_unit) coprod -> 'a2 paths

val recomplf :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a1 -> 'a2

val weqrecomplf :
  'a1 -> 'a2 -> 'a1 isisolated -> 'a2 isisolated -> ('a1 compl, 'a2 compl)
  weq -> ('a1, 'a2) weq

val homotrecomplfhomot :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> ('a1 compl ->
  'a2 compl) -> ('a1 compl, 'a2 compl) homot -> ('a1, 'a2) homot

val pathsrecomplfxtoy :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a2 paths

val homotrecomplfcomp :
  'a1 -> 'a2 -> 'a3 -> 'a1 isisolated -> 'a2 isisolated -> ('a1 compl -> 'a2
  compl) -> ('a2 compl -> 'a3 compl) -> ('a1, 'a3) homot

val homotrecomplfidfun : 'a1 -> 'a1 isisolated -> ('a1, 'a1) homot

val ishomotinclrecomplf :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a1 compl ->
  'a2 compl -> 'a2 paths -> 'a2 compl paths

val funtranspos0 : 'a1 -> 'a1 -> 'a1 isisolated -> 'a1 compl -> 'a1 compl

val homottranspos0t2t1t1t2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1 compl, 'a1 compl)
  homot

val weqtranspos0 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1 compl, 'a1 compl) weq

val funtranspos : 'a1 isolated -> 'a1 isolated -> 'a1 -> 'a1

val homottranspost2t1t1t2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) homot

val weqtranspos :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) weq

val pathsfuntransposoft1 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 paths

val pathsfuntransposoft2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 paths

val pathsfuntransposofnet1t2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 -> 'a1 paths neg ->
  'a1 paths neg -> 'a1 paths

val homotfuntranspos2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) homot

val eqbx : 'a1 -> 'a1 isisolated -> 'a1 -> bool

val iscontrhfibereqbx : 'a1 -> 'a1 isisolated -> ('a1, bool) hfiber iscontr

type ('x, 'y) bhfiber = ('x, bool) hfiber

val weqhfibertobhfiber :
  ('a1 -> 'a2) -> 'a2 -> 'a2 isisolated -> (('a1, 'a2) hfiber, ('a1, 'a2)
  bhfiber) weq

val isinclii1 : ('a1, ('a1, 'a2) coprod) isincl

val iscontrhfiberii1x : 'a1 -> ('a1, ('a1, 'a2) coprod) hfiber iscontr

val neghfiberii1y : 'a2 -> ('a1, ('a1, 'a2) coprod) hfiber neg

val isinclii2 : ('a2, ('a1, 'a2) coprod) isincl

val iscontrhfiberii2y : 'a2 -> ('a2, ('a1, 'a2) coprod) hfiber iscontr

val neghfiberii2x : 'a1 -> ('a2, ('a1, 'a2) coprod) hfiber neg

val negintersectii1ii2 :
  ('a1, 'a2) coprod -> ('a1, ('a1, 'a2) coprod) hfiber -> ('a2, ('a1, 'a2)
  coprod) hfiber -> empty

val isolatedtoisolatedii1 :
  'a1 -> 'a1 isisolated -> ('a1, 'a2) coprod isisolated

val isolatedtoisolatedii2 :
  'a2 -> 'a2 isisolated -> ('a1, 'a2) coprod isisolated

val weqhfibercoprodf1 :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a3 -> (('a1, 'a3) hfiber, (('a1, 'a2)
  coprod, ('a3, 'a4) coprod) hfiber) weq

val weqhfibercoprodf2 :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a4 -> (('a2, 'a4) hfiber, (('a1, 'a2)
  coprod, ('a3, 'a4) coprod) hfiber) weq

val isofhlevelfcoprodf :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a4)
  isofhlevelf -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) isofhlevelf

val isofhlevelsnsummand1 :
  nat -> ('a1, 'a2) coprod isofhlevel -> 'a1 isofhlevel

val isofhlevelsnsummand2 :
  nat -> ('a1, 'a2) coprod isofhlevel -> 'a2 isofhlevel

val isofhlevelssncoprod :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) coprod isofhlevel

val isasetcoprod : 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) coprod isaset

val coprodofhfiberstohfiber :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a3) hfiber, ('a2, 'a3)
  hfiber) coprod -> (('a1, 'a2) coprod, 'a3) hfiber

val hfibertocoprodofhfibers :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a2) coprod, 'a3) hfiber ->
  (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) coprod

val weqhfibersofsumofmaps :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> ((('a1, 'a3) hfiber, ('a2, 'a3)
  hfiber) coprod, (('a1, 'a2) coprod, 'a3) hfiber) weq

val isofhlevelfssnsumofmaps :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> (('a1, 'a2) coprod, 'a3) isofhlevelf

val noil1 :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
  ('a1, 'a3) hfiber -> ('a2, 'a3) hfiber -> empty

val weqhfibernoi1 :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
  ('a1, 'a3) hfiber -> ((('a1, 'a2) coprod, 'a3) hfiber, ('a1, 'a3) hfiber)
  weq

val weqhfibernoi2 :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
  ('a2, 'a3) hfiber -> ((('a1, 'a2) coprod, 'a3) hfiber, ('a2, 'a3) hfiber)
  weq

val isofhlevelfsumofmapsnoi :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1 -> 'a2 -> 'a3 paths neg) -> (('a1, 'a2) coprod, 'a3)
  isofhlevelf

val tocompltoii1x : 'a1 -> ('a1 compl, 'a2) coprod -> ('a1, 'a2) coprod compl

val fromcompltoii1x :
  'a1 -> ('a1, 'a2) coprod compl -> ('a1 compl, 'a2) coprod

val isweqtocompltoii1x :
  'a1 -> (('a1 compl, 'a2) coprod, ('a1, 'a2) coprod compl) isweq

val tocompltoii2y : 'a2 -> ('a1, 'a2 compl) coprod -> ('a1, 'a2) coprod compl

val fromcompltoii2y :
  'a2 -> ('a1, 'a2) coprod compl -> ('a1, 'a2 compl) coprod

val isweqtocompltoii2y :
  'a2 -> (('a1, 'a2 compl) coprod, ('a1, 'a2) coprod compl) isweq

val tocompltodisjoint : 'a1 -> ('a1, coq_unit) coprod compl

val fromcompltodisjoint : ('a1, coq_unit) coprod compl -> 'a1

val isweqtocompltodisjoint : ('a1, ('a1, coq_unit) coprod compl) isweq

(* val weqtocompltodisjoint : ('a1, ('a1, coq_unit) coprod compl) weq *)

(* val isweqfromcompltodisjoint : (('a1, coq_unit) coprod compl, 'a1) isweq *)

val isdecpropif' :
  'a1 isaprop -> ('a1, 'a1 neg) coprod -> ('a1, 'a1 neg) coprod iscontr

val isdecproppaths : 'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 paths isdecprop

val isdeceqif : ('a1 -> 'a1 -> 'a1 paths isdecprop) -> 'a1 isdeceq

val isaninv1 : 'a1 isdecprop -> 'a1 isaninvprop

val isdecpropfibseq1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a1
  isdecprop -> 'a3 isaprop -> 'a2 isdecprop

val isdecpropfibseq0 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
  isdecprop -> 'a3 isdeceq -> 'a1 isdecprop

val isdecpropdirprod :
  'a1 isdecprop -> 'a2 isdecprop -> ('a1, 'a2) dirprod isdecprop

val fromneganddecx :
  'a1 isdecprop -> ('a1, 'a2) dirprod neg -> ('a1 neg, 'a2 neg) coprod

val fromneganddecy :
  'a2 isdecprop -> ('a1, 'a2) dirprod neg -> ('a1 neg, 'a2 neg) coprod

val isdecproppathsfromisolated :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isdecprop

val isdecproppathstoisolated :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isdecprop

type ('x, 'y) isdecincl = 'y -> ('x, 'y) hfiber isdecprop

val isdecincltoisincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> ('a1, 'a2) isincl

val isdecinclfromisweq :
  ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isdecincl

val isdecpropfromdecincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> 'a2 isdecprop -> 'a1 isdecprop

val isdecinclii1 : ('a1, ('a1, 'a2) coprod) isdecincl

val isdecinclii2 : ('a2, ('a1, 'a2) coprod) isdecincl

val isdecinclpr1 :
  ('a1 -> 'a2 isdecprop) -> (('a1, 'a2) total2, 'a1) isdecincl

val isdecinclhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2) isdecincl
  -> ('a1, 'a2) isdecincl

val isdecinclcomp :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isdecincl -> ('a2, 'a3)
  isdecincl -> ('a1, 'a3) isdecincl

val isdecinclf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isdecincl
  -> ('a1, 'a2) isdecincl

val isdecinclg :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a1, 'a3) isdecincl ->
  ('a2, 'a3) isdecincl

val isisolateddecinclf :
  ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) isdecincl -> 'a1 isisolated -> 'a2
  isisolated

type ('x, 'y) negimage = ('y, ('x, 'y) hfiber neg) total2

val make_negimage :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber neg -> ('a2, ('a1, 'a2) hfiber
  neg) total2

val isinclfromcoprodwithnegimage :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> (('a1, ('a2, ('a1, 'a2) hfiber neg)
  total2) coprod, 'a2) isincl

type ('x, 'y) iscoproj =
  (('x, ('y, ('x, 'y) hfiber neg) total2) coprod, 'y) isweq

val weqcoproj :
  ('a1 -> 'a2) -> ('a1, 'a2) iscoproj -> (('a1, ('a1, 'a2) negimage) coprod,
  'a2) weq

val iscoprojfromisdecincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> ('a1, 'a2) iscoproj

val isdecinclfromiscoproj :
  ('a1 -> 'a2) -> ('a1, 'a2) iscoproj -> ('a1, 'a2) isdecincl
