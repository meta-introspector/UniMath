open PartA
open Preamble
open UnivalenceAxiom

(** val funextsec_toforallpaths :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a2) paths
    paths **)

let funextsec_toforallpaths f g h =
  pathsinv0 h
    (invmap (Obj.magic weqtoforallpaths f g)
      (pr1weq (Obj.magic weqtoforallpaths f g) h))
    (homotinvweqweq0 (Obj.magic weqtoforallpaths f g) h)

(** val toforallpaths_funextsec :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2) homot
    paths **)

let toforallpaths_funextsec f g h =
  homotweqinvweq (Obj.magic weqtoforallpaths f g) h
