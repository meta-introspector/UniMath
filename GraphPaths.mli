open PartA
open Preamble

type __ = Obj.t

type ('v, 'e) issymmetric = 'v -> 'v -> ('e, 'e) weq

type ('v, 'e) gpaths_of_length = __

type ('v, 'e) gpaths = (nat, ('v, 'e) gpaths_of_length) total2

val nil : 'a1 -> ('a1, 'a2) gpaths

val cons : 'a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2) gpaths -> ('a1, 'a2) gpaths

val gpaths_ind :
  'a1 -> 'a3 -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2) gpaths -> 'a3 -> 'a3) -> 'a1
  -> ('a1, 'a2) gpaths -> 'a3

val foldr :
  'a1 -> ('a1 -> 'a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> 'a1 -> ('a1, 'a2) gpaths
  -> 'a3

val concat :
  'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> ('a1, 'a2) gpaths -> ('a1, 'a2)
  gpaths

val append :
  'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> 'a2 -> ('a1, 'a2) gpaths

val reverse :
  ('a1, 'a2) issymmetric -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> ('a1, 'a2)
  gpaths

type ('v, 'e) symmetric_closure = ('e, 'e) coprod

(* val issymmetric_symmetric_closure : *)
(*   ('a1, ('a1, 'a2) symmetric_closure) issymmetric *)

val reverse_in_closure :
  'a1 -> 'a1 -> ('a1, ('a1, 'a2) symmetric_closure) gpaths -> ('a1, ('a1,
  'a2) symmetric_closure) gpaths
