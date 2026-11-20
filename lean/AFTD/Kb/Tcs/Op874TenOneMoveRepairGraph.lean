import AFTD.Prelude
import AFTD.Kb.Tcs.Op874TenOneMoveRepairData

/-!
# op874_ten_one_move_repair_graph

Topic: graphs   Node: 866e00f6382d

Provenance: helper lemma. Ten-vertex one-move repair obstruction, experiment 36336.

The cubic base of the ten-vertex repair obstruction.
-/

def op874_ten_one_move_repair_graph : SimpleGraph (Fin 10) := SimpleGraph.fromEdgeSet (↑In1098TenRepair.edges : Set (Sym2 (Fin 10)))
