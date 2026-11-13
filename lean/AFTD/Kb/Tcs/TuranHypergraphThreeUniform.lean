import AFTD.Prelude
import AFTD.Kb.Tcs.TuranHypergraph
import AFTD.Kb.Tcs.IsThreeUniform

/-!
# turan_hypergraph_three_uniform

Topic: combinatorics   Node: 02ca5f8b93a8

Provenance: helper lemma. arXiv:2611.16654:380

For every natural number n, the balanced 3-partite Turán hypergraph T_n is 3-uniform.
-/

/-- The Turán construction T_n is 3-uniform. -/
theorem turan_hypergraph_three_uniform (n : ℕ) : is_three_uniform (turan_hypergraph n) := fun _ he => (Finset.mem_filter.mp he).2.1
