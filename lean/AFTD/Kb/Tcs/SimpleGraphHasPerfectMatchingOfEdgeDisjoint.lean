import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEdgeDisjointPerfectMatchings

/-!
# simple_graph_has_perfect_matching_of_edge_disjoint

Topic: graphs   Node: 339fc6af7670

Provenance: helper lemma. folklore

If a simple graph G contains at least k pairwise edge-disjoint perfect matchings for some k > 0, then G contains a perfect matching.
-/

/-- If a graph has at least k pairwise edge-disjoint perfect matchings with k > 0, it has a perfect matching. -/
theorem simple_graph_has_perfect_matching_of_edge_disjoint {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 0 < k)
    (h : simple_graph_has_edge_disjoint_perfect_matchings G k) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  rcases h with ⟨M, hM, -⟩
  exact ⟨M ⟨0, hk⟩, hM ⟨0, hk⟩⟩
