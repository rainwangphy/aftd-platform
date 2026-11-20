import AFTD.Prelude
import AFTD.Kb.Tcs.Op874TwelveVertexNoMatchingCutEdges

/-!
# op874_twelve_vertex_no_matching_cut_graph

Topic: graphs   Node: 6bcc7dcb706a

Provenance: helper lemma. Explicit 12-vertex obstruction to the OP-874 perfect-matching-cut route, experiment 35469.

The simple graph with the displayed eighteen edges.
-/

def op874_twelve_vertex_no_matching_cut_graph : SimpleGraph (Fin 12) := SimpleGraph.fromEdgeSet (↑op874_twelve_vertex_no_matching_cut_edges : Set (Sym2 (Fin 12)))
