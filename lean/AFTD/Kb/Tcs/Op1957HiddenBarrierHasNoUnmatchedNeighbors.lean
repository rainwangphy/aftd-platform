import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957HiddenBarrierGraph

/-!
# op1957_hidden_barrier_has_no_unmatched_neighbors

Topic: graphs   Node: 7e3b959231a7

Provenance: helper lemma. OP-1957; hidden barrier relaxation, experiment 40492.

The opposite-side hub has no neighbor in the specified six-vertex unmatched set.
-/

theorem op1957_hidden_barrier_has_no_unmatched_neighbors :
    ∀ u ∈ in1209_hidden_U, ¬ op1957_hidden_barrier_graph.Adj u 20 := by
  set_option maxHeartbeats 4000000 in
    decide
