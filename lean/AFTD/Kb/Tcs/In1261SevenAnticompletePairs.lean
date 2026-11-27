import AFTD.Prelude
import AFTD.Kb.Tcs.In1261SevenGraph
import AFTD.Kb.Tcs.In1261SevenForbiddenOrdered

/-!
# in1261_seven_anticomplete_pairs

Topic: graphs   Node: f533790272ee

Provenance: helper lemma. OP-1957: finite seven-by-seven control from experiment 43349; related problem arXiv:2611.22690.

The first and second displayed blocks of the explicit graph are anticomplete, as are the third and fourth blocks.
-/

set_option maxHeartbeats 4000000
set_option linter.all false
local instance  aftdLocal_2a60f20893e61368_0 : DecidableRel in1261_seven_graph.Adj := by
  unfold in1261_seven_graph in1261_seven_forbidden_ordered
  infer_instance

theorem in1261_seven_anticomplete_pairs:
    (∀ a ∈ ({0,1,2,3,4,5,6} : Finset (Fin 28)),
      ∀ b ∈ ({7,8,9,10,11,12,13} : Finset (Fin 28)), ¬ in1261_seven_graph.Adj a b) ∧
    (∀ c ∈ ({14,15,16,17,18,19,20} : Finset (Fin 28)),
      ∀ d ∈ ({21,22,23,24,25,26,27} : Finset (Fin 28)), ¬ in1261_seven_graph.Adj c d) := by
  decide
