open PartB
open Preamble

val isaproptotal2 :
  ('a1, 'a2) isPredicate -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) -> ('a1,
  'a2) total2 isaprop
