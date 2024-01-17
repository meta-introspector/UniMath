open PartA
open PartA0
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t

val funextsec_toforallpaths :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a2) paths
  paths

val toforallpaths_funextsec :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2) homot paths

val toforallpaths_funextsec_comp :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1, 'a2) homot -> ('a1, 'a2) homot) paths

val maponpaths_funextsec :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) homot -> 'a2 paths paths

val weqonsec :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> ('a1 -> 'a3, 'a2 -> 'a4) weq

val weq_transportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) weq

val weq_transportf_comp : 'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths

val weqonpaths2 :
  ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
  ('a1 paths, 'a2 paths) weq

val eqweqmap_ap : 'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths

val eqweqmap_ap' : 'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths

val pr1_eqweqmap : __ paths -> ('a1 -> 'a2) paths

val path_to_fun : __ paths -> 'a1 -> 'a2

val pr1_eqweqmap2 : coq_UU paths -> ('a1 -> 'a2) paths

val weqpath_transport : ('a1, 'a2) weq -> ('a1 -> 'a2) paths

(* val weqpath_cast : ('a1, 'a2) weq -> ('a1 -> 'a2) paths *)

(* val switch_weq : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a1 paths *)

(* val switch_weq' : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths *)

(* val weq_over_sections : *)
(*   ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths -> *)
(*   (('a2 -> 'a3) -> ('a4, 'a5) weq) -> ((('a2 -> 'a3, 'a4) total2, 'a3) *)
(*   hfiber, (('a1 -> 'a3, 'a5) total2, 'a3) hfiber) weq *)

(* val maponpaths_app_homot : *)
(*   ('a2 -> 'a1 -> 'a3) -> ('a2 -> 'a1 -> 'a3) -> (('a2, 'a1) dirprod -> 'a3 *)
(*   paths) -> 'a1 -> 'a2 -> 'a3 paths paths *)

(* val path_path_fun : *)
(*   ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a2) paths -> *)
(*   ('a1 -> 'a2 paths paths) -> ('a1 -> 'a2) paths paths *)
