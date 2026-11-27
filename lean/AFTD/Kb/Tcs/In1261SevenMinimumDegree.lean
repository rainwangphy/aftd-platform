import AFTD.Prelude
import AFTD.Kb.Tcs.In1261SevenGraph
import AFTD.Kb.Tcs.In1261SevenForbiddenOrdered

/-!
# in1261_seven_minimum_degree

Topic: graphs   Node: 49f35f9838af

Provenance: helper lemma. OP-1957: finite seven-by-seven control from experiment 43349; related problem arXiv:2611.22690.

Every vertex of the explicit seven-by-seven control graph has degree at least sixteen.
-/

set_option maxHeartbeats 4000000
set_option linter.all false
local instance  aftdLocal_dfd3bb8d36cafc2d_0 : DecidableRel in1261_seven_graph.Adj := by
  unfold in1261_seven_graph in1261_seven_forbidden_ordered
  infer_instance

theorem in1261_seven_minimum_degree:
    ∀ v : Fin 28, 16 ≤ (in1261_seven_graph.neighborFinset v).card := by
  intro v
  fin_cases v <;> decide
