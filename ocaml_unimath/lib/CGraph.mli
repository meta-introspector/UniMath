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

val node_set : cgraph -> hSet

val isaset_arc : cgraph -> arc isaset

val arc_set : cgraph -> hSet

type is_cgraph_mor = (arc -> node paths, arc -> node paths) dirprod

type cgraph_mor = (node -> node, (arc -> arc, is_cgraph_mor) total2) total2

val make_cgraph_mor :
  precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> is_cgraph_mor
  -> cgraph_mor

val onnode : precgraph -> precgraph -> cgraph_mor -> node -> node

val onarc : precgraph -> precgraph -> cgraph_mor -> arc -> arc

val preserves_source :
  precgraph -> precgraph -> cgraph_mor -> arc -> node paths

val preserves_target :
  precgraph -> precgraph -> cgraph_mor -> arc -> node paths

val is_cgraph_mor_id : precgraph -> is_cgraph_mor

val cgraph_mor_id : precgraph -> cgraph_mor

val is_cgraph_mor_comp :
  precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
  is_cgraph_mor

val cgraph_mor_comp :
  precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
  cgraph_mor

val cgraph_mor_id_left :
  precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths

val cgraph_mor_id_right :
  precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths

val cgraph_mor_comp_assoc :
  precgraph -> precgraph -> precgraph -> precgraph -> cgraph_mor ->
  cgraph_mor -> cgraph_mor -> cgraph_mor paths

val isaprop_is_cgraph_mor :
  precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> has_nodeset ->
  is_cgraph_mor isaprop

val isaset_cgraph_mor :
  precgraph -> precgraph -> has_nodeset -> has_arcset -> cgraph_mor isaset

val cgraph_mor_eq_aux :
  precgraph -> precgraph -> cgraph_mor -> cgraph_mor -> (node -> node) paths
  -> (arc -> arc) paths -> has_nodeset -> cgraph_mor paths

val cgraph_mor_eq :
  cgraph -> cgraph -> cgraph_mor -> cgraph_mor -> (node -> node paths) ->
  (arc -> arc paths) -> cgraph_mor paths

val precgraph_weq_pregraph : (precgraph, pregraph) weq
