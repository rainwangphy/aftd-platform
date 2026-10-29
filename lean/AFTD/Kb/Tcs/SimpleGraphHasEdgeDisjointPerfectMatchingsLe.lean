import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEdgeDisjointPerfectMatchings

/-!
# simple_graph_has_edge_disjoint_perfect_matchings_le

Topic: graphs   Node: 980f1863f93c

Provenance: helper lemma. step towards op_652_half_degree_packing_negation

If a simple graph G has at least k pairwise edge-disjoint perfect matchings and m ≤ k, then G has at least m pairwise edge-disjoint perfect matchings.
-/

/-- If a graph has at least k edge-disjoint perfect matchings, it also has at least m for any m ≤ k. -/
theorem simple_graph_has_edge_disjoint_perfect_matchings_le
    {V : Type*} (G : SimpleGraph V) {k m : ℕ} (hkm : m ≤ k)
    (h : simple_graph_has_edge_disjoint_perfect_matchings G k) :
    simple_graph_has_edge_disjoint_perfect_matchings G m := by
  rcases h with ⟨M, hperf, hdisj⟩
  refine ⟨fun i => M (Fin.castLE hkm i), fun i => hperf _, ?_⟩
  intro i j hij
  exact hdisj fun hc => hij (Fin.castLE_injective hkm hc)
