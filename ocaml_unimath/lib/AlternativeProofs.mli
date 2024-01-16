open PartA
open Preamble

type coq_PathPair =()
    
val total2_paths_equiv' :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths, ('a1,
  'a2) coq_PathPair) weq

val total2_paths_equiv'_compute :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths -> ('a1,
  'a2) coq_PathPair) paths
