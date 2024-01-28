open CRelationClasses
open Datatypes

(** val on_snd : ('a2 -> 'a3) -> ('a1, 'a2) prod -> ('a1, 'a3) prod **)

let on_snd f p =
  Coq_pair ((fst p), (f (snd p)))

(** val test_snd : ('a2 -> bool) -> ('a1, 'a2) prod -> bool **)

let test_snd f p =
  f (snd p)

(** val map_pair :
    ('a1 -> 'a2) -> ('a3 -> 'a4) -> ('a1, 'a3) prod -> ('a2, 'a4) prod **)

let map_pair f g p =
  Coq_pair ((f (fst p)), (g (snd p)))

(** val on_pi2 :
    ('a2 -> 'a2) -> (('a1, 'a2) prod, 'a3) prod -> (('a1, 'a2) prod, 'a3) prod **)

let on_pi2 f p =
  Coq_pair ((Coq_pair ((fst (fst p)), (f (snd (fst p))))), (snd p))

(** val swap : ('a1, 'a2) prod -> ('a2, 'a1) prod **)

let swap x =
  Coq_pair ((snd x), (fst x))

(** val and_assum : 'a1 -> ('a1 -> 'a2) -> ('a1, 'a2) prod **)

let and_assum f f' =
  Coq_pair (f, (f' f))

type ('p1, 'p2, 'p3) and3 =
| Times3 of 'p1 * 'p2 * 'p3

type ('p1, 'p2, 'p3, 'p4) and4 =
| Times4 of 'p1 * 'p2 * 'p3 * 'p4

type ('p1, 'p2, 'p3, 'p4, 'p5) and5 =
| Times5 of 'p1 * 'p2 * 'p3 * 'p4 * 'p5

type ('p1, 'p2, 'p3, 'p4, 'p5, 'p6) and6 =
| Times6 of 'p1 * 'p2 * 'p3 * 'p4 * 'p5 * 'p6

type ('p1, 'p2, 'p3, 'p4, 'p5, 'p6, 'p7) and7 =
| Times7 of 'p1 * 'p2 * 'p3 * 'p4 * 'p5 * 'p6 * 'p7

type ('p1, 'p2, 'p3, 'p4, 'p5, 'p6, 'p7, 'p8) and8 =
| Times8 of 'p1 * 'p2 * 'p3 * 'p4 * 'p5 * 'p6 * 'p7 * 'p8

type ('p1, 'p2, 'p3, 'p4, 'p5, 'p6, 'p7, 'p8, 'p9) and9 =
| Times9 of 'p1 * 'p2 * 'p3 * 'p4 * 'p5 * 'p6 * 'p7 * 'p8 * 'p9

type ('p1, 'p2, 'p3, 'p4, 'p5, 'p6, 'p7, 'p8, 'p9, 'p10) and10 =
| Times10 of 'p1 * 'p2 * 'p3 * 'p4 * 'p5 * 'p6 * 'p7 * 'p8 * 'p9 * 'p10

(** val coq_Prod_reflexivity :
    ('a1, 'a2) coq_Reflexive -> ('a1, 'a3) coq_Reflexive -> ('a1, ('a2, 'a3)
    prod) coq_Reflexive **)

let coq_Prod_reflexivity x x0 x1 =
  Coq_pair ((reflexivity x x1), (reflexivity x0 x1))
