open PartA
open PartB
open PartD
open Preamble
open Propositions0
open UnivalenceAxiom

type __ = Obj.t

type pregraph = (coq_UU, __) total2

val make_pregraph : pregraph

type vertex = __

type edge = __

type has_vertexset = vertex isaset

val isaprop_has_vertexset : pregraph -> has_vertexset isaprop

type has_edgesets = vertex -> vertex -> edge isaset

type graph = (pregraph, (has_vertexset, has_edgesets) dirprod) total2

val make_graph : pregraph -> has_vertexset -> has_edgesets -> graph

val pregraph_of_graph : graph -> pregraph

val isaset_vertex : graph -> vertex isaset

val isaset_edge : graph -> vertex -> vertex -> edge isaset

type graph_mor = (vertex -> vertex, vertex -> vertex -> edge -> edge) total2

val make_graph_mor :
  pregraph -> pregraph -> (vertex -> vertex) -> (vertex -> vertex -> edge ->
  edge) -> graph_mor

val onvertex : pregraph -> pregraph -> graph_mor -> vertex -> vertex

val onedge :
  pregraph -> pregraph -> graph_mor -> vertex -> vertex -> edge -> edge

val graph_mor_id : pregraph -> graph_mor

val graph_mor_comp :
  pregraph -> pregraph -> pregraph -> graph_mor -> graph_mor -> graph_mor

val make_graph_mor_eq :
  pregraph -> pregraph -> (vertex -> vertex) -> (vertex -> vertex -> edge ->
  edge) -> (vertex -> vertex -> edge -> edge) -> (vertex -> vertex -> edge ->
  edge paths) -> graph_mor paths

val graph_mor_id_left : pregraph -> pregraph -> graph_mor -> graph_mor paths

val graph_mor_id_right : pregraph -> pregraph -> graph_mor -> graph_mor paths

val graph_mor_comp_assoc :
  pregraph -> pregraph -> pregraph -> pregraph -> graph_mor -> graph_mor ->
  graph_mor -> graph_mor paths

(* val isaset_graph_mor : *)
(*   pregraph -> pregraph -> has_vertexset -> has_edgesets -> graph_mor isaset *)
