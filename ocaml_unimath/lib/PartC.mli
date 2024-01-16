open PartA
open PartB
open Preamble

val isinclii1 : ('a1, ('a1, 'a2) coprod) isincl

val isinclii2 : ('a2, ('a1, 'a2) coprod) isincl

val weqhfibercoprodf1 :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a3 -> (('a1, 'a3) hfiber, (('a1, 'a2)
  coprod, ('a3, 'a4) coprod) hfiber) weq

val weqhfibercoprodf2 :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a4 -> (('a2, 'a4) hfiber, (('a1, 'a2)
  coprod, ('a3, 'a4) coprod) hfiber) weq

val isofhlevelfcoprodf :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a4)
  isofhlevelf -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) isofhlevelf

val isofhlevelssncoprod :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) coprod isofhlevel

val isasetcoprod : 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) coprod isaset
