import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ThreeCoreRepairData

/-!
# op874_three_core_repair_graph

Topic: graphs   Node: 424cbb5bc60e

Provenance: helper lemma. Three-core uniform-port repair obstruction, experiment 36363.

The explicit cubic base of the three-core repair obstruction.
-/

def op874_three_core_repair_graph : SimpleGraph (Fin 30) := SimpleGraph.fromEdgeSet (↑In1098ThreeCore.edges : Set (Sym2 (Fin 30)))
