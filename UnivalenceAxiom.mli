open PartA
open PartB
open Preamble

type __ = Obj.t

val eqweqmap : coq_UU paths -> ('a1, 'a2) weq

val sectohfiber :
  ('a1 -> 'a2) -> ('a1 -> ('a1, 'a2) total2, 'a1 -> 'a1) hfiber

val hfibertosec : ('a1 -> ('a1, 'a2) total2, 'a1 -> 'a1) hfiber -> 'a1 -> 'a2

val sectohfibertosec : ('a1 -> 'a2) -> ('a1 -> 'a2) paths

val isweqtransportf10 : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

val isweqtransportb10 : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

val l1 :
  coq_UU paths -> 'a3 -> (__ -> __ -> (__, __) weq -> 'a3 -> 'a3) -> (__ ->
  'a3 -> 'a3 paths) -> 'a3 paths

type univalenceStatement = __ -> __ -> (coq_UU paths, (__, __) weq) isweq

type funextemptyStatement =
  __ -> (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

type propositionalUnivalenceStatement =
  __ -> __ -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __) -> coq_UU
  paths

type funcontrStatement = __ -> __ -> (__ -> __ iscontr) -> (__ -> __) iscontr

type funextcontrStatement =
  __ -> __ -> (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr

type isweqtoforallpathsStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot)
  isweq

type funextsecStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

type funextfunStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

type weqtopathsStatement = __ -> __ -> (__, __) weq -> coq_UU paths

type weqpathsweqStatement = __ -> __ -> (__, __) weq -> (__, __) weq paths

type weqtoforallpathsStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot)
  weq

val funextsecImplication :
  isweqtoforallpathsStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot
  -> (__ -> __) paths

val funextfunImplication :
  funextsecStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ ->
  __) paths

val univfromtwoaxioms :
  ((weqtopathsStatement, weqpathsweqStatement) total2, univalenceStatement)
  logeq

val univalenceUAH : univalenceStatement -> (coq_UU paths, ('a1, 'a2) weq) weq

val weqtopathsUAH : univalenceStatement -> (__, __) weq -> coq_UU paths

val weqpathsweqUAH : univalenceStatement -> (__, __) weq -> (__, __) weq paths

val propositionalUnivalenceUAH :
  univalenceStatement -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __)
  -> coq_UU paths

val weqtransportbUAH :
  univalenceStatement -> (__ -> __ -> (__, __) weq -> 'a1 -> 'a1) -> (__ ->
  'a1 -> 'a1 paths) -> ('a2, 'a3) weq -> 'a1 -> 'a1 paths

val isweqweqtransportbUAH :
  univalenceStatement -> (__ -> __ -> (__, __) weq -> 'a1 -> 'a1) -> (__ ->
  'a1 -> 'a1 paths) -> ('a2, 'a3) weq -> ('a1, 'a1) isweq

val isweqcompwithweqUAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq

val eqcor0UAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2 -> 'a3) ->
  ('a1 -> 'a3) paths -> ('a2 -> 'a3) paths

val apathpr1toprUAH : univalenceStatement -> ('a1 pathsspace -> 'a1) paths

val funextfunPreliminaryUAH :
  univalenceStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ ->
  __) paths

val funextemptyUAH :
  univalenceStatement -> (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val isweqlcompwithweqUAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq

val isweqrcompwithweqUAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a3 -> 'a1, 'a3 -> 'a2) isweq

val funcontrUAH :
  univalenceStatement -> (__ -> __ iscontr) -> (__ -> __) iscontr

val funextcontrUAH :
  univalenceStatement -> (__ -> __) -> (__ -> __, __ -> __ paths) total2
  iscontr

val isweqtoforallpathsUAH :
  univalenceStatement -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__,
  __) homot) isweq

val funcontrFromUnivalence :
  univalenceStatement -> (__ -> __ iscontr) -> (__ -> __) iscontr

val funextsecweqFromUnivalence :
  univalenceStatement -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__,
  __) homot) isweq

val funextemptyFromUnivalence :
  univalenceStatement -> (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val propositionalUnivalenceFromUnivalence :
  univalenceStatement -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __)
  -> coq_UU paths

val funextcontrStatementFromUnivalence :
  univalenceStatement -> (__ -> __) -> (__ -> __, __ -> __ paths) total2
  iscontr

val univalenceAxiom : (coq_UU paths, (__, __) weq) isweq

val funextemptyAxiom : (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val isweqtoforallpathsAxiom :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq

val funcontrAxiom : (__ -> __ iscontr) -> (__ -> __) iscontr

val propositionalUnivalenceAxiom :
  __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __) -> coq_UU paths

val funextcontrAxiom : (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr

val funextempty : (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val univalence : (coq_UU paths, ('a1, 'a2) weq) weq

val weqtopaths : (__, __) weq -> coq_UU paths

val weqpathsweq : (__, __) weq -> (__, __) weq paths

val funcontr : (__ -> __ iscontr) -> (__ -> __) iscontr

val funextcontr : (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr

val isweqtoforallpaths :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq

val weqtoforallpaths :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) weq

val funextsec : (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

val funextfun : (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

val weqfunextsec :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1, 'a2) homot, ('a1 -> 'a2) paths) weq

val funcontrtwice : ('a1 -> 'a1 -> 'a2 iscontr) -> ('a1 -> 'a1 -> 'a2) iscontr

val toforallpaths_induction :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1 -> 'a2) paths -> 'a3) -> ('a1 -> 'a2
  paths) -> 'a3

val transportf_funextfun :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> 'a1 -> 'a3 -> 'a3
  paths

(* val coq_UU_rect : (coq_UU paths -> 'a3) -> ('a1, 'a2) weq -> 'a3 *)
