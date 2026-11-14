import AFTD.Prelude
import AFTD.Kb.Tcs.TripartiteTuranHypergraph
import AFTD.Kb.Tcs.IsThreeUniform

/-!
# tripartite_turan_hypergraph_three_uniform

Topic: combinatorics   Node: ea84700e29b3

Provenance: helper lemma. arXiv:2611.16654 Section 3

For any family of finite sets V : ZMod 3 → Finset α, the tripartite Turán hypergraph tripartite_turan_hypergraph V is 3-uniform (is_three_uniform).
-/

/-- The tripartite Turán hypergraph is 3-uniform. -/
theorem tripartite_turan_hypergraph_three_uniform {α : Type*} [DecidableEq α]
    (V : ZMod 3 → Finset α) : is_three_uniform (tripartite_turan_hypergraph V) := by
  intro e he
  simp only [tripartite_turan_hypergraph, Finset.mem_filter, Finset.mem_powersetCard] at he
  exact he.1.2
