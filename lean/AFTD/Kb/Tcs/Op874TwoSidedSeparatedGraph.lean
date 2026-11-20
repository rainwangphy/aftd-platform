import AFTD.Prelude
import AFTD.Kb.Tcs.Op874TwoSidedSeparatedEdges

/-!
# op874_two_sided_separated_graph

Topic: graphs   Node: eed716ed8c76

Provenance: helper lemma. Explicit two-orientation separated-ownership obstruction, experiment 35686.

The explicit simple graph used for the two-orientation obstruction.
-/

def op874_two_sided_separated_graph : SimpleGraph (Fin 168) := SimpleGraph.fromEdgeSet (↑op874_two_sided_separated_edges : Set (Sym2 (Fin 168)))
