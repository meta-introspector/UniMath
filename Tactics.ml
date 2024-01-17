open PartA
(* open PartB *)
(* open Preamble *)

(** val post_cat :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths **)

let post_cat x y z p q =
  pathscomp0 x y z q p

(** val pre_cat : 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths **)

let pre_cat =
  pathscomp0

(** val iscontrweqb' : 'a2 iscontr -> ('a1, 'a2) weq -> 'a1 iscontr **)

let iscontrweqb' is w =
  iscontrweqb w is

(** val isaprop_goal : 'a1 isaprop -> ('a1 isaprop -> 'a1) -> 'a1 **)

let isaprop_goal ig f =
  f ig
