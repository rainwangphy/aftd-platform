import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEndpointSumEdges
import AFTD.Kb.Tcs.RegularGraphComplRegularIff

/-!
# simple_graph_endpoint_sum_edges_subset

Topic: graphs   Node: 3c91ce690479

Provenance: helper lemma. arXiv:2611.16338, Section 2

For any finite simple graph G, vertex labeling φ : V → ℕ, and natural number r, the finset simple_graph_endpoint_sum_edges G φ r is a subset of the edge finset of G.
-/

open scoped Classical in
/-- Every edge with endpoint sum r is an edge of G. -/
theorem simple_graph_endpoint_sum_edges_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (φ : V → ℕ) (r : ℕ) :
    simple_graph_endpoint_sum_edges G φ r ⊆ G.edgeFinset := by first | exact regular_graph_compl_regular_iff | (apply regular_graph_compl_regular_iff <;> assumption) | (apply regular_graph_compl_regular_iff <;> simp_all) | simpa using regular_graph_compl_regular_iff | (simp only [simple_graph_endpoint_sum_edges] at *; first | exact regular_graph_compl_regular_iff | (apply regular_graph_compl_regular_iff <;> assumption) | (apply regular_graph_compl_regular_iff <;> simp_all) | simpa using regular_graph_compl_regular_iff)
