import AFTD.Prelude
import AFTD.Kb.Tcs.Op874TwoSidedFiveEdges

/-!
# op874_two_sided_five_graph

Topic: graphs   Node: b8753229c274

Provenance: helper lemma. Two-sided fixed-factor five-cycle obstruction, experiment 35839.

The explicit graph carrying the displayed cycle factor and matching.
-/

def op874_two_sided_five_graph : SimpleGraph (Fin 60) := SimpleGraph.fromEdgeSet (↑op874_two_sided_five_edges : Set (Sym2 (Fin 60)))
