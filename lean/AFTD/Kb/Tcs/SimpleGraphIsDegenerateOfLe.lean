import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDegenerate

/-!
# simple_graph_is_degenerate_of_le

Topic: graphs   Node: c32a72b99711

Provenance: formalization of a published result. Source: arXiv:2611.04674, Section 1

If a simple graph G is a subgraph of G' (meaning G ≤ G') and G' is k-degenerate, then G is also k-degenerate.
-/

/-- Any subgraph of a k-degenerate graph is k-degenerate. -/
theorem simple_graph_is_degenerate_of_le {V : Type*} {G G' : SimpleGraph V} (h : G ≤ G') {k : ℕ}
    (hG' : simple_graph_is_degenerate G' k) : simple_graph_is_degenerate G k := by
  intro s hs
  obtain ⟨v, hv, hcard⟩ := hG' s hs
  refine ⟨v, hv, le_trans (Set.encard_le_encard ?_) hcard⟩
  exact Set.inter_subset_inter_right s (SimpleGraph.neighborSet_mono h v)
