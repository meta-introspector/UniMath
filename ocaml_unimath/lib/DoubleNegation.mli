open PartA
open PartB
open Propositions

val wma_dneg : 'a2 dneg -> ('a2 -> 'a1 neg) -> 'a1 neg

val dneg_decidable : 'a1 decidable dneg

val wma_decidable : ('a2 decidable -> 'a1 neg) -> 'a1 neg

val negforall_to_existsneg' : hProptoType -> hProptoType dneg
