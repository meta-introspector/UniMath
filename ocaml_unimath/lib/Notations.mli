open PartA
open PartB
open Preamble
open Propositions

val hequiv : hProp -> hProp -> hProp

val total2_hProp : hProp -> (hProptoType -> hProp) -> hProp

type 'x paths_from = 'x coconusfromt

val point_to : 'a1 -> 'a1 paths_from -> 'a1

val paths_from_path : 'a1 -> 'a1 paths_from -> 'a1 paths

type 'x paths' = 'x paths

val idpath' : 'a1 -> 'a1 paths'

type 'x paths_to = 'x coconustot

val point_from : 'a1 -> 'a1 paths_to -> 'a1

val paths_to_path : 'a1 -> 'a1 paths_to -> 'a1 paths

val iscontr_paths_to : 'a1 -> 'a1 paths_to iscontr

val iscontr_paths_from : 'a1 -> 'a1 paths_from iscontr

val paths_to_prop : 'a1 -> hProp

val paths_from_prop : 'a1 -> hProp

val squash_path : 'a1 -> 'a1 -> hProptoType paths
