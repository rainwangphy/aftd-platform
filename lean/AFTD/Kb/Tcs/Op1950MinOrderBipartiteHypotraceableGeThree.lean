import AFTD.Prelude
import AFTD.Kb.Tcs.MinOrderBipartiteHypotraceable
import AFTD.Kb.Tcs.SimpleGraphIsHypotraceable

/-!
# op_1950_min_order_bipartite_hypotraceable_ge_three

Topic: graphs   Node: 67f21ab50eac

Provenance: helper lemma. arXiv:2611.23018, Section 3, Question 8

If there exists a 2-colorable hypotraceable simple graph on a finite vertex type of cardinality at least 3, then the minimum order of a bipartite hypotraceable graph is at least 3.
-/

open scoped Classical in
/-- If a bipartite hypotraceable graph of order at least 3 exists, the minimum order is at least 3. -/
theorem op_1950_min_order_bipartite_hypotraceable_ge_three
    (h : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.Colorable 2 ∧ G.IsHypotraceable ∧ 3 ≤ Fintype.card V) :
    3 ≤ min_order_bipartite_hypotraceable := by
  unfold min_order_bipartite_hypotraceable
  obtain ⟨V, fV, G, hcol, hhyp, hcard⟩ := h
  refine le_csInf ?_ ?_
  · exact ⟨Fintype.card V, V, fV, rfl, G, hcol, hhyp, hcard⟩
  · rintro n ⟨W, fW, hn, H, _, _, h3⟩
    exact h3
