import AFTD.Prelude
import AFTD.Kb.Tcs.Op874InterleavedFiveEdges

/-!
# op874_interleaved_five_graph

Topic: graphs   Node: 74b650b2b78c

Provenance: helper lemma. Interleaved fixed-factor obstruction, experiments 35864 and 35866.

The explicit graph carrying the displayed cycle factor and matching.
-/

def op874_interleaved_five_graph : SimpleGraph (Fin 60) := SimpleGraph.fromEdgeSet (↑op874_interleaved_five_edges : Set (Sym2 (Fin 60)))
