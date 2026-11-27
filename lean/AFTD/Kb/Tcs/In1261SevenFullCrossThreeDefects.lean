import AFTD.Prelude
import AFTD.Kb.Tcs.In1261SevenGraph
import AFTD.Kb.Tcs.In1261SevenForbiddenOrdered

/-!
# in1261_seven_full_cross_three_defects

Topic: graphs   Node: 8eec972ca014

Provenance: helper lemma. OP-1957: finite seven-by-seven control from experiment 43349; related problem arXiv:2611.22690.

In the explicit seven-by-seven control graph, vertex 0 is adjacent to the whole third block and exactly three vertices of the first block are nonadjacent to vertex 14.
-/

set_option maxHeartbeats 4000000
set_option linter.all false
local instance  aftdLocal_4177c105032b32a5_0 : DecidableRel in1261_seven_graph.Adj := by
  unfold in1261_seven_graph in1261_seven_forbidden_ordered
  infer_instance

theorem in1261_seven_full_cross_three_defects:
    (∀ y : Fin 28, y ∈ ({14,15,16,17,18,19,20} : Finset (Fin 28)) → in1261_seven_graph.Adj 0 y) ∧
    (({0,1,2,3,4,5,6} : Finset (Fin 28)).filter (fun a => ¬ in1261_seven_graph.Adj a 14)).card = 3 := by
  decide
