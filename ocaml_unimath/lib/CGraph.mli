open Graph
open PartA
open PartB
open PartD
open PartD0
open Preamble
open Propositions0
open Sets
open UnivalenceAxiom

type __ = Obj.t

type precgraph =
  (coq_UU, (coq_UU, (__ -> __, __ -> __) dirprod) total2) total2

val make_precgraph : ('a2 -> 'a1) -> ('a2 -> 'a1) -> precgraph

type node = __

type arc = __

val source : precgraph -> arc -> node

val target : precgraph -> arc -> node

type has_nodeset = node isaset

type has_arcset = arc isaset

type cgraph = (precgraph, (node isaset, arc isaset) dirprod) total2

val make_cgraph : precgraph -> node isaset -> arc isaset -> cgraph

val precgraph_of_cgraph : cgraph -> precgraph

val isaset_node : cgraph -> node isaset

