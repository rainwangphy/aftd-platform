import AFTD.Prelude
import AFTD.Kb.Tcs.Op874HallObstructionFactorEdges
import AFTD.Kb.Tcs.Op874HallObstructionMatching

/-!
# op874_hall_obstruction_base

Topic: graphs   Node: f2790e0e2958

Provenance: helper lemma. Explicit paired-odd-cycle interaction obstruction in OP-874, experiment 35342.

The explicit cubic graph formed by the cycle edges and the matching.
-/

def op874_hall_obstruction_base : SimpleGraph (Fin 40) := SimpleGraph.fromEdgeSet (↑(op874_hall_obstruction_factor_edges ∪ op874_hall_obstruction_matching) : Set (Sym2 (Fin 40)))
