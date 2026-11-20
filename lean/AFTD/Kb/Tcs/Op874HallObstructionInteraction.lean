import AFTD.Prelude
import AFTD.Kb.Tcs.Op874HallObstructionMatching
import AFTD.Kb.Tcs.Op874HallObstructionCycleIndex

/-!
# op874_hall_obstruction_interaction

Topic: graphs   Node: 9e32b739b694

Provenance: helper lemma. Explicit paired-odd-cycle interaction obstruction in OP-874, experiment 35342.

The simple interaction graph induced by the prescribed matching between the eight factor cycles.
-/

def op874_hall_obstruction_interaction : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet (↑(op874_hall_obstruction_matching.image (Sym2.map op874_hall_obstruction_cycle_index)) : Set (Sym2 (Fin 8)))
