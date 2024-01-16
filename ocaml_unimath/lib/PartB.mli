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

type ('x, 'y) isofhlevelf = 'y -> ('x, 'y) hfiber isofhlevel

val isofhlevelfhomot :
  nat -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2)
  isofhlevelf -> ('a1, 'a2) isofhlevelf

val isofhlevelffromXY :
  nat -> ('a1 -> 'a2) -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2)
  isofhlevelf

val isofhlevelXfromfY :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> 'a2 isofhlevel -> 'a1
  isofhlevel

val isofhlevelfhfiberpr1y :
  nat -> ('a1 -> 'a2) -> 'a2 -> ('a2 -> 'a2 paths isofhlevel) -> (('a1, 'a2)
  hfiber, 'a1) isofhlevelf

val isofhlevelfsnfib :
  nat -> 'a1 -> 'a1 paths isofhlevel -> ('a2, ('a1, 'a2) total2) isofhlevelf

val isofhlevelfhfiberpr1 :
  nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 isofhlevel -> (('a1, 'a2) hfiber, 'a1)
  isofhlevelf

val isofhlevelff :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1, 'a2) isofhlevelf

val isofhlevelfgf :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1, 'a3) isofhlevelf

type 'x isaprop = 'x isofhlevel

val isapropifcontr : 'a1 iscontr -> 'a1 isaprop

val hlevelntosn : nat -> 'a1 isofhlevel -> 'a1 isofhlevel

val isofhlevelcontr : nat -> 'a1 iscontr -> 'a1 isofhlevel

val isofhlevelfweq : nat -> ('a1, 'a2) weq -> ('a1, 'a2) isofhlevelf

val weqhfibertocontr :
  ('a1 -> 'a2) -> 'a2 -> 'a2 iscontr -> (('a1, 'a2) hfiber, 'a1) weq

val weqhfibertounit : (('a1, coq_unit) hfiber, 'a1) weq

val isofhleveltofun : nat -> 'a1 isofhlevel -> ('a1, coq_unit) isofhlevelf

val isofhlevelfromfun : nat -> ('a1, coq_unit) isofhlevelf -> 'a1 isofhlevel

val isofhlevelsnprop : nat -> 'a1 isaprop -> 'a1 isofhlevel

val iscontraprop1 : 'a1 isaprop -> 'a1 -> 'a1 iscontr

val iscontraprop1inv : ('a1 -> 'a1 iscontr) -> 'a1 isaprop

type ('x, 'y) isincl = ('x, 'y) isofhlevelf

val iscontrhfiberofincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> ('a1, 'a2) hfiber iscontr

val samehfibers :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> 'a2 -> (('a1, 'a2)
  hfiber, ('a1, 'a3) hfiber) weq

type 'x isaset = 'x -> 'x -> 'x paths isaprop

val isasetunit : coq_unit isaset

val isofhlevelssnset : nat -> 'a1 isaset -> 'a1 isofhlevel

type 'x decidable = ('x, 'x neg) coprod

type 'x isdeceq = 'x -> 'x -> 'x paths decidable

val isdeceqbool : bool isdeceq

type 'x isisolated = 'x -> ('x paths, 'x paths neg) coprod

val isaproppathsfromisolated :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop

val isasetifdeceq : 'a1 isdeceq -> 'a1 isaset

val isasetbool : bool isaset
