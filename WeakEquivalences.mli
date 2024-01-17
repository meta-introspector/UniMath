open PartA
open Preamble

val transitive_paths_weq :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) weq

(* val weqtotal2comm : *)
(*   (('a1, ('a2, 'a3) total2) total2, ('a2, ('a1, 'a3) total2) total2) weq *)

val pathsdirprodweq :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (('a1, 'a2) dirprod paths, ('a1 paths, 'a2
  paths) dirprod) weq

(* val dirprod_with_contr_r : 'a1 iscontr -> ('a2, ('a2, 'a1) dirprod) weq *)

(* val dirprod_with_contr_l : 'a1 iscontr -> ('a2, ('a1, 'a2) dirprod) weq *)

(* val total2_assoc_fun_left : *)
(*   (('a1 -> ('a2, 'a3) total2, 'a4) total2, ('a1 -> 'a2, ('a1 -> 'a3, 'a4) *)
(*   total2) total2) weq *)

(* val sec_total2_distributivity : *)
(*   ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq *)
