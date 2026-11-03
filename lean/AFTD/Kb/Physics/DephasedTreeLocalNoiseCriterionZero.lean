import AFTD.Prelude
import AFTD.Kb.Physics.DephasedTreeLocalNoiseCriterion
import AFTD.Kb.Tcs.TwoLeSimpleGraphTreeEstimate

/-!
# dephased_tree_local_noise_criterion_zero

Topic: quantum_mechanics   Node: 8193098fcf98

Provenance: helper lemma. folklore

For any finite simple graph T on vertex type V, the identically zero noise profile q = fun _ => 0 satisfies dephased_tree_local_noise_criterion T (fun _ => 0).
-/

/-- The local noise criterion holds unconditionally for the identically zero noise profile on any finite graph. -/
theorem dephased_tree_local_noise_criterion_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] :
    dephased_tree_local_noise_criterion T (fun _ => 0) := by first | exact two_le_simple_graph_tree_estimate | (apply two_le_simple_graph_tree_estimate <;> assumption) | (apply two_le_simple_graph_tree_estimate <;> simp_all) | simpa using two_le_simple_graph_tree_estimate | (simp only [dephased_tree_local_noise_criterion] at *; first | exact two_le_simple_graph_tree_estimate | (apply two_le_simple_graph_tree_estimate <;> assumption) | (apply two_le_simple_graph_tree_estimate <;> simp_all) | simpa using two_le_simple_graph_tree_estimate)
