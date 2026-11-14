import AFTD.Prelude

/-!
# simple_graph_unique_path_of_weight_lt_half_girth

Topic: combinatorics   Node: fc5e0cde7813

Provenance: helper lemma. arXiv:2611.15755 Appendix B, Lemma B.1 -- Asymptotically Optimal Bounds for Counting Near-Minimum Circuits in Regular Matroids

Let G be a simple graph, let ω : Sym2 V → ℝ be a nonnegative edge weight function (0 ≤ ω e for all e ∈ G.edgeSet), and let gw > 0. If every cycle in G has total edge weight at least gw, then between any two vertices u and v in G, there is at most one path of total edge weight strictly less than gw / 2.
-/

open scoped BigOperators in
open Classical in
/-- Between any two vertices, there is at most one path of weight strictly less than half the weighted girth in a nonnegative-weighted graph. -/
theorem simple_graph_unique_path_of_weight_lt_half_girth {V : Type*}
    (G : SimpleGraph V) (ω : Sym2 V → ℝ) (hω : ∀ e ∈ G.edgeSet, 0 ≤ ω e)
    (gw : ℝ) (hgw : 0 < gw)
    (hgirth : ∀ (u : V) (p : G.Walk u u), p.IsCycle → gw ≤ (p.edges.map ω).sum)
    {u v : V} (p₁ p₂ : G.Walk u v) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hw₁ : (p₁.edges.map ω).sum < gw / 2)
    (hw₂ : (p₂.edges.map ω).sum < gw / 2) :
    p₁ = p₂ := by
  by_contra hne
  obtain ⟨a, b, p', q', hp', hq', hc⟩ := hp₁.exists_isCycle_of_ne hp₂ hne
  let c := p'.append q'.reverse
  have hcedges : c.edges = p'.edges ++ q'.edges.reverse := by
    simp [c]
  have hsub : c.edges.Sublist (p₁.edges ++ p₂.edges.reverse) := by
    rw [hcedges]
    exact (hp'.edges_isInfix.sublist.append (hq'.edges_isInfix.sublist.reverse))
  have hnonneg : ∀ e ∈ p₁.edges ++ p₂.edges.reverse, 0 ≤ ω e := by
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact hω e (p₁.edges_subset_edgeSet he)
    · exact hω e (p₂.edges_subset_edgeSet (by simpa using he))
  have hsumle : (c.edges.map ω).sum ≤ (p₁.edges.map ω).sum + (p₂.edges.map ω).sum := by
    have hs := List.Sublist.sum_le_sum (hsub.map ω) (by
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨e, he, rfl⟩ := ha
      exact hnonneg e he)
    simpa [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse] using hs
  have hgwle : gw ≤ (c.edges.map ω).sum := hgirth a c hc
  linarith
