import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957HiddenBarrierGraph

/-!
# op1957_hidden_barrier_min_degree

Topic: graphs   Node: 6743a959530e

Provenance: helper lemma. OP-1957; hidden barrier relaxation, experiment 40492.

Every vertex in the hidden-barrier graph has degree at least 21.
-/

theorem op1957_hidden_barrier_min_degree :
    ∀ v, 21 ≤ (op1957_hidden_barrier_graph.neighborFinset v).card := by
  set_option maxHeartbeats 4000000 in
    decide
