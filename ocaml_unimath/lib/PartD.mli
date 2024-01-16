open PartA
open PartB
open Preamble
open UnivalenceAxiom

val impred : nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel

val impred_isaprop : ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2) isaprop

val isapropimpl : 'a2 isaprop -> ('a1 -> 'a2) isaprop
