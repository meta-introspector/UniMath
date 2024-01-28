open PartA
open Preamble

type __ = Obj.t

type 'x isofhlevel = __

val hlevelretract :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 isofhlevel
  -> 'a2 isofhlevel

val isofhlevelweqf : nat -> ('a1, 'a2) weq -> 'a1 isofhlevel -> 'a2 isofhlevel

val isofhlevelweqb : nat -> ('a1, 'a2) weq -> 'a2 isofhlevel -> 'a1 isofhlevel

val isofhlevelsn : nat -> ('a1 -> 'a1 isofhlevel) -> 'a1 isofhlevel

val isofhlevelssn : nat -> ('a1 -> 'a1 paths isofhlevel) -> 'a1 isofhlevel

type ('x, 'y) isofhlevelf = 'y -> ('x, 'y) hfiber isofhlevel

val isofhlevelfhomot :
  nat -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2)
  isofhlevelf -> ('a1, 'a2) isofhlevelf

val isofhlevelfpmap :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> (('a1, 'a3) total2, ('a2,
  'a3) total2) isofhlevelf

val isofhlevelfffromZ :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr ->
  'a3 isofhlevel -> ('a1, 'a2) isofhlevelf

val isofhlevelXfromg :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr ->
  ('a2, 'a3) isofhlevelf -> 'a1 isofhlevel

val isofhlevelffromXY :
  nat -> ('a1 -> 'a2) -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2)
  isofhlevelf

val isofhlevelXfromfY :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> 'a2 isofhlevel -> 'a1
  isofhlevel

val isofhlevelffib :
  nat -> 'a1 -> ('a1 -> 'a1 paths isofhlevel) -> ('a2, ('a1, 'a2) total2)
  isofhlevelf

val isofhlevelfhfiberpr1y :
  nat -> ('a1 -> 'a2) -> 'a2 -> ('a2 -> 'a2 paths isofhlevel) -> (('a1, 'a2)
  hfiber, 'a1) isofhlevelf

val isofhlevelfsnfib :
  nat -> 'a1 -> 'a1 paths isofhlevel -> ('a2, ('a1, 'a2) total2) isofhlevelf

val isofhlevelfsnhfiberpr1 :
  nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 paths isofhlevel -> (('a1, 'a2) hfiber,
  'a1) isofhlevelf

val isofhlevelfhfiberpr1 :
  nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 isofhlevel -> (('a1, 'a2) hfiber, 'a1)
  isofhlevelf

val isofhlevelff :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1, 'a2) isofhlevelf

val isofhlevelfgf :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1, 'a3) isofhlevelf

val isofhlevelfgwtog :
  nat -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2,
  'a3) isofhlevelf

val isofhlevelfgtogw :
  nat -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) isofhlevelf -> ('a1,
  'a3) isofhlevelf

val isofhlevelfhomot2 :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) weq -> ('a1 -> 'a3 paths)
  -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3) isofhlevelf

val isofhlevelfonpaths :
  nat -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> ('a1, 'a2) isofhlevelf -> ('a1 paths,
  'a2 paths) isofhlevelf

val isofhlevelfsn :
  nat -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> ('a1 paths, 'a2 paths) isofhlevelf)
  -> ('a1, 'a2) isofhlevelf

val isofhlevelfssn :
  nat -> ('a1 -> 'a2) -> ('a1 -> ('a1 paths, 'a2 paths) isofhlevelf) -> ('a1,
  'a2) isofhlevelf

val isofhlevelfpr1 :
  nat -> ('a1 -> 'a2 isofhlevel) -> (('a1, 'a2) total2, 'a1) isofhlevelf

val isweqpr1 : ('a1 -> 'a2 iscontr) -> (('a1, 'a2) total2, 'a1) isweq

val weqpr1 : ('a1 -> 'a2 iscontr) -> (('a1, 'a2) total2, 'a1) weq

val isofhleveltotal2 :
  nat -> 'a1 isofhlevel -> ('a1 -> 'a2 isofhlevel) -> ('a1, 'a2) total2
  isofhlevel

val isofhleveldirprod :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) dirprod isofhlevel

type 'x isaprop = 'x isofhlevel

type ('x, 'y) isPredicate = 'x -> 'y isaprop

val isapropunit : coq_unit isaprop

val isapropdirprod : 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) dirprod isaprop

val isapropifcontr : 'a1 iscontr -> 'a1 isaprop

val hlevelntosn : nat -> 'a1 isofhlevel -> 'a1 isofhlevel

val isofhlevelcontr : nat -> 'a1 iscontr -> 'a1 isofhlevel

val isofhlevelfweq : nat -> ('a1, 'a2) weq -> ('a1, 'a2) isofhlevelf

val isweqfinfibseq :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a3
  iscontr -> ('a1, 'a2) isweq

val weqhfibertocontr :
  ('a1 -> 'a2) -> 'a2 -> 'a2 iscontr -> (('a1, 'a2) hfiber, 'a1) weq

val weqhfibertounit : (('a1, coq_unit) hfiber, 'a1) weq

val isofhleveltofun : nat -> 'a1 isofhlevel -> ('a1, coq_unit) isofhlevelf

val isofhlevelfromfun : nat -> ('a1, coq_unit) isofhlevelf -> 'a1 isofhlevel

val weqhfiberunit :
  ('a1 -> 'a2) -> 'a2 -> (('a1, (coq_unit, 'a2) hfiber) total2, ('a1, 'a2)
  hfiber) weq

val isofhlevelsnprop : nat -> 'a1 isaprop -> 'a1 isofhlevel

val iscontraprop1 : 'a1 isaprop -> 'a1 -> 'a1 iscontr

val iscontraprop1inv : ('a1 -> 'a1 iscontr) -> 'a1 isaprop

type 'x isProofIrrelevant = 'x -> 'x -> 'x paths

val proofirrelevance : 'a1 isaprop -> 'a1 isProofIrrelevant

val invproofirrelevance : 'a1 isProofIrrelevant -> 'a1 isaprop

val isProofIrrelevant_paths :
  'a1 isProofIrrelevant -> 'a1 -> 'a1 -> 'a1 paths isProofIrrelevant

val isapropcoprod :
  'a1 isaprop -> 'a2 isaprop -> ('a1 -> 'a2 -> empty) -> ('a1, 'a2) coprod
  isaprop

val isweqimplimpl :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2)
  isweq

val weqimplimpl :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) weq

val weqiff : ('a1, 'a2) logeq -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) weq

val weq_to_iff : ('a1, 'a2) weq -> ('a1, 'a2) logeq

val isapropempty : empty isaprop

val isapropifnegtrue : ('a1 -> empty) -> 'a1 isaprop

val isapropretract :
  'a2 isaprop -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a1) homot -> 'a1
  isaprop

val isapropcomponent1 : ('a1, 'a2) coprod isaprop -> 'a1 isaprop

val isapropcomponent2 : ('a1, 'a2) coprod isaprop -> 'a2 isaprop

type ('x, 'y) isincl = ('x, 'y) isofhlevelf

type ('x, 'y) incl = ('x -> 'y, ('x, 'y) isincl) total2

val make_incl : ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) incl

val pr1incl : ('a1, 'a2) incl -> 'a1 -> 'a2

val isinclweq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isincl

val isofhlevelfsnincl :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) isofhlevelf

val weqtoincl : ('a1, 'a2) weq -> ('a1, 'a2) incl

val isinclcomp : ('a1, 'a2) incl -> ('a2, 'a3) incl -> ('a1, 'a3) isincl

val inclcomp : ('a1, 'a2) incl -> ('a2, 'a3) incl -> ('a1, 'a3) incl

val isincltwooutof3a :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isincl ->
  ('a1, 'a2) isincl

val isinclgwtog :
  ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) isincl -> ('a2, 'a3) isincl

val isinclgtogw :
  ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isincl

val isinclhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) isincl ->
  ('a1, 'a2) isincl

val isofhlevelsninclb :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a2 isofhlevel -> 'a1 isofhlevel

val isapropinclb :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a2 isaprop -> 'a1 isaprop

val iscontrhfiberofincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> ('a1, 'a2) hfiber iscontr

type ('x, 'y) isInjective = 'x -> 'x -> ('x paths, 'y paths) isweq

val coq_Injectivity :
  ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> 'a1 -> 'a1 -> ('a1 paths, 'a2
  paths) weq

val isweqonpathsincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) isInjective

val weqonpathsincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths)
  weq

val invmaponpathsincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths

val isinclweqonpaths :
  ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> ('a1, 'a2) isincl

val isinclpr1 : ('a1 -> 'a2 isaprop) -> (('a1, 'a2) total2, 'a1) isincl

val subtypeInjectivity :
  ('a1, 'a2) isPredicate -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1,
  'a2) total2 paths, 'a1 paths) weq

val subtypePath :
  ('a1, 'a2) isPredicate -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1
  paths -> ('a1, 'a2) total2 paths

val subtypePath' :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 isaprop -> ('a1,
  'a2) total2 paths

val unique_exists :
  'a1 -> 'a2 -> ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2 -> 'a1 paths) -> ('a1,
  'a2) total2 iscontr

val subtypePairEquality :
  ('a1, 'a2) isPredicate -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1,
  'a2) total2 paths

val subtypePairEquality' :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 isaprop -> ('a1, 'a2) total2
  paths

val samehfibers :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> 'a2 -> (('a1, 'a2)
  hfiber, ('a1, 'a3) hfiber) weq

type 'x isaset = 'x -> 'x -> 'x paths isaprop

val isasetunit : coq_unit isaset

val isasetempty : empty isaset

val isasetifcontr : 'a1 iscontr -> 'a1 isaset

val isasetaprop : 'a1 isaprop -> 'a1 isaset

val isaset_total2 :
  'a1 isaset -> ('a1 -> 'a2 isaset) -> ('a1, 'a2) total2 isaset

val isaset_dirprod : 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) dirprod isaset

val isaset_hfiber :
  ('a1 -> 'a2) -> 'a2 -> 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) hfiber isaset

val uip :
  'a1 isaset -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val isofhlevelssnset : nat -> 'a1 isaset -> 'a1 isofhlevel

val isasetifiscontrloops : ('a1 -> 'a1 paths iscontr) -> 'a1 isaset

val iscontrloopsifisaset : 'a1 isaset -> 'a1 -> 'a1 paths iscontr

val isasetsubset :
  ('a1 -> 'a2) -> 'a2 isaset -> ('a1, 'a2) isincl -> 'a1 isaset

val isinclfromhfiber :
  ('a1 -> 'a2) -> 'a2 isaset -> 'a2 -> (('a1, 'a2) hfiber, 'a1) isincl

val isinclbetweensets :
  ('a1 -> 'a2) -> 'a1 isaset -> 'a2 isaset -> ('a1 -> 'a1 -> 'a2 paths -> 'a1
  paths) -> ('a1, 'a2) isincl

val isinclfromunit : (coq_unit -> 'a1) -> 'a1 isaset -> (coq_unit, 'a1) isincl

val set_bijection_to_weq :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_UniqueConstruction -> 'a2 isaset -> ('a1,
  'a2) isweq

type ('p, 'q) complementary = ('p -> 'q -> empty, ('p, 'q) coprod) dirprod

val complementary_to_neg_iff :
  ('a1, 'a2) complementary -> ('a1 neg, 'a2) logeq

type 'x decidable = ('x, 'x neg) coprod

val decidable_to_complementary : 'a1 decidable -> ('a1, 'a1 neg) complementary

val decidable_dirprod :
  'a1 decidable -> 'a2 decidable -> ('a1, 'a2) dirprod decidable

type 'p isdecprop = (('p, 'p neg) coprod, 'p isaprop) dirprod

val isdecproptoisaprop : 'a1 isdecprop -> 'a1 isaprop

val isdecpropif : 'a1 isaprop -> ('a1, 'a1 neg) coprod -> 'a1 isdecprop

val isdecpropfromiscontr : 'a1 iscontr -> 'a1 isdecprop

val isdecpropempty : empty isdecprop

val isdecpropweqf : ('a1, 'a2) weq -> 'a1 isdecprop -> 'a2 isdecprop

val isdecpropweqb : ('a1, 'a2) weq -> 'a2 isdecprop -> 'a1 isdecprop

val isdecproplogeqf :
  'a1 isdecprop -> 'a2 isaprop -> ('a1, 'a2) logeq -> 'a2 isdecprop

val isdecproplogeqb :
  'a1 isaprop -> 'a2 isdecprop -> ('a1, 'a2) logeq -> 'a1 isdecprop

val isdecpropfromneg : 'a1 neg -> 'a1 isdecprop

type 'x isdeceq = 'x -> 'x -> 'x paths decidable

val isdeceqweqf : ('a1, 'a2) weq -> 'a1 isdeceq -> 'a2 isdeceq

val isdeceqweqb : ('a1, 'a2) weq -> 'a2 isdeceq -> 'a1 isdeceq

val isdeceqinclb :
  ('a1 -> 'a2) -> 'a2 isdeceq -> ('a1, 'a2) isincl -> 'a1 isdeceq

val isdeceqifisaprop : 'a1 isaprop -> 'a1 isdeceq

val booleq : 'a1 isdeceq -> 'a1 -> 'a1 -> bool

val eqfromdnegeq : 'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 paths dneg -> 'a1 paths

val isdecequnit : coq_unit isdeceq

val isdeceqbool : bool isdeceq

val isdeceqcoprod : 'a1 isdeceq -> 'a2 isdeceq -> ('a1, 'a2) coprod isdeceq

type 'x isisolated = 'x -> ('x paths, 'x paths neg) coprod

type 't isolated = ('t, 't isisolated) total2

val make_isolated : 'a1 -> 'a1 isisolated -> 'a1 isolated

val pr1isolated : 'a1 isolated -> 'a1

val isaproppathsfromisolated :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop

val isaproppathstoisolated : 'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop

val isisolatedweqf : ('a1, 'a2) weq -> 'a1 -> 'a1 isisolated -> 'a2 isisolated

val isisolatedinclb :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a2 isisolated -> 'a1 isisolated

val disjointl1 : ('a1, coq_unit) coprod isisolated

val isasetifdeceq : 'a1 isdeceq -> 'a1 isaset

val isdeceq_total2 :
  'a1 isdeceq -> ('a1 -> 'a2 isdeceq) -> ('a1, 'a2) total2 isdeceq

val isolfun1 : 'a1 -> 'a1 isisolated -> 'a2 -> 'a2 -> 'a1 -> 'a2

val decfun1 : 'a1 isdeceq -> 'a1 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val isolfun2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a2 -> 'a2 -> 'a2 -> 'a1
  -> 'a2

val decfun2 : 'a1 isdeceq -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val isolfun3 :
  'a1 -> 'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 isisolated ->
  'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val decfun3 :
  'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val isasetbool : bool isaset

val subsetsplit :
  ('a1 -> bool) -> 'a1 -> (('a1, bool) hfiber, ('a1, bool) hfiber) coprod

val subsetsplitinv :
  ('a1 -> bool) -> (('a1, bool) hfiber, ('a1, bool) hfiber) coprod -> 'a1

val weqsubsetsplit :
  ('a1 -> bool) -> ('a1, (('a1, bool) hfiber, ('a1, bool) hfiber) coprod) weq
