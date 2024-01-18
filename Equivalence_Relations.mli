open GraphPaths
open Preamble
open Propositions
open Sets

val eqrel_closure_hrel : 'a1 hrel -> 'a1 hrel

val iseqrel_closure : 'a1 hrel -> 'a1 iseqrel

val eqrel_closure : 'a1 hrel -> 'a1 eqrel

val eqrel_closure_minimal :
  'a1 hrel -> 'a1 eqrel -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> 'a1
  -> 'a1 -> hProptoType -> hProptoType
