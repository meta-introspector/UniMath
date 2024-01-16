open Preamble
open Propositions
open Sets
open UnivalenceAxiom

val squash_to_hSet :
  hSet -> ('a1 -> pr1hSet) -> hProptoType -> hProptoType -> pr1hSet

val squash_to_hSet_2' :
  hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType ->
  hProptoType -> pr1hSet

val eqset_to_path : hSet -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths
