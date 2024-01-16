open PartA
open PartB
open Preamble

val retract_dec :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2, 'a2) homot -> 'a1 isdeceq -> 'a2
  isdeceq

val logeq_dec : ('a1, 'a2) logeq -> 'a1 decidable -> 'a2 decidable
