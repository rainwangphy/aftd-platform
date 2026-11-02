import AFTD.Prelude

/-!
# digraph_cross_boundary_predecessor

Topic: graphs   Node: c76c2d3ab6b0

Provenance: helper lemma. Boundary reduction for the minimum-counterexample route to OP-110.

For any bipartition of an arc-dominated digraph, every tail of a crossing arc has an in-neighbor that is also a tail of a crossing arc.
-/

theorem digraph_cross_boundary_predecessor {α : Type} (D : Digraph α) (p : α → Bool) (hdom : ∀ u v, D.Adj u v → ∃ w, D.Adj w u ∧ D.Adj w v) (v : α) (hv : ∃ x, D.Adj v x ∧ p v ≠ p x) : ∃ w, D.Adj w v ∧ ∃ y, D.Adj w y ∧ p w ≠ p y := by
  obtain ⟨x, hvx, hx⟩ := hv
  obtain ⟨w, hwv, hwx⟩ := hdom v x hvx
  refine ⟨w, hwv, ?_⟩
  by_cases h : p w = p v
  · exact ⟨x, hwx, fun he => hx (h.symm.trans he)⟩
  · exact ⟨v, hwv, h⟩
