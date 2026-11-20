import AFTD.Prelude
import AFTD.Kb.Tcs.Op874OneSidedEdges

/-!
# op874_one_sided_graph

Topic: graphs   Node: 71c4191b3093

Provenance: helper lemma. Explicit fixed-factor orientation obstruction, experiments 35726–35727.

The explicit graph with the indicated cycle factor and matching.
-/

def op874_one_sided_graph : SimpleGraph (Fin 36) := SimpleGraph.fromEdgeSet (↑op874_one_sided_edges : Set (Sym2 (Fin 36)))
