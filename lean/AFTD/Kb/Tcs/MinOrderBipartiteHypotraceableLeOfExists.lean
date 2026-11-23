import AFTD.Prelude
import AFTD.Kb.Tcs.MinOrderBipartiteHypotraceable
import AFTD.Kb.Tcs.SimpleGraphIsHypotraceable

/-!
# min_order_bipartite_hypotraceable_le_of_exists

Topic: graphs   Node: a184ba1007d2

Provenance: helper lemma. step towards op_1950_min_order_bipartite_hypotraceable_lt_two_hundred

If there exists a 2-colorable hypotraceable simple graph on a finite vertex type of cardinality n with 3 ≤ n, then min_order_bipartite_hypotraceable ≤ n.
-/

open scoped Classical in
/-- If there exists a 2-colorable hypotraceable simple graph on a finite vertex type of cardinality n with 3 ≤ n, then min_order_bipartite_hypotraceable ≤ n. -/
theorem min_order_bipartite_hypotraceable_le_of_exists
    {n : ℕ} (hn : 3 ≤ n)
    (h : ∃ (V : Type) (_ : Fintype V) (_ : Fintype.card V = n) (G : SimpleGraph V),
      G.Colorable 2 ∧ G.IsHypotraceable) :
    min_order_bipartite_hypotraceable ≤ n := by
  obtain ⟨V, hV, hcard, G, hcol, hhypo⟩ := h
  unfold min_order_bipartite_hypotraceable
  apply Nat.sInf_le
  exact ⟨V, hV, hcard, G, hcol, hhypo, hn⟩
