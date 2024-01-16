open PartA
open PartB
open Preamble
open Propositions
open Sets

val isTotalOrder : hSet -> pr1hSet hrel -> hProp

val tot_nge_to_le :
  hSet -> pr1hSet hrel -> pr1hSet istotal -> pr1hSet -> pr1hSet ->
  hProptoType -> hProptoType

val tot_nle_iff_gt :
  hSet -> pr1hSet hrel -> hProptoType -> pr1hSet -> pr1hSet -> (hProptoType,
  hProptoType) logeq
