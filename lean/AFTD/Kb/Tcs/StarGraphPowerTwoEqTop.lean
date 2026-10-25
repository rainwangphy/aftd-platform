import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# star_graph_power_two_eq_top

Topic: graphs   Node: 07a362ee19a3

Provenance: helper lemma. arXiv:2610.13852 Theorem 6.3 proof

For any natural number m, the square of the star graph on m + 1 vertices is the complete graph.
-/

/-- The square of a star graph on m + 1 vertices is the complete graph. -/
theorem star_graph_power_two_eq_top (m : ℕ) :
    simple_graph_power (SimpleGraph.starGraph (0 : Fin (m + 1))) 2 = ⊤ := by
  have hadj : ∀ a b : Fin (m+1), (SimpleGraph.starGraph (0 : Fin (m+1))).Adj a b ↔ a ≠ b ∧ (a = 0 ∨ b = 0) := by
    intro a b
    simp [SimpleGraph.starGraph, SimpleGraph.fromRel_adj]
  have hdist : ∀ u v : Fin (m+1), u ≠ v →
      (SimpleGraph.starGraph (0 : Fin (m + 1))).edist u v ≤ ((2:ℕ) : ℕ∞) := by
    intro u v h
    rcases eq_or_ne u 0 with hu | hu
    · have hav : (SimpleGraph.starGraph (0 : Fin (m+1))).Adj u v := (hadj u v).2 ⟨h, Or.inl hu⟩
      have h1 := SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hav SimpleGraph.Walk.nil)
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
      exact h1.trans (by simp)
    · rcases eq_or_ne v 0 with hv | hv
      · have hav : (SimpleGraph.starGraph (0 : Fin (m+1))).Adj u v := (hadj u v).2 ⟨h, Or.inr hv⟩
        have h1 := SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hav SimpleGraph.Walk.nil)
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
        exact h1.trans (by simp)
      · have hav1 : (SimpleGraph.starGraph (0 : Fin (m+1))).Adj u 0 := (hadj u 0).2 ⟨hu, Or.inr rfl⟩
        have hav2 : (SimpleGraph.starGraph (0 : Fin (m+1))).Adj 0 v := (hadj 0 v).2 ⟨fun hh => hv hh.symm, Or.inl rfl⟩
        have h1 := SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons hav1 (SimpleGraph.Walk.cons hav2 SimpleGraph.Walk.nil))
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
        exact h1.trans (by simp)
  ext u v
  simp only [simple_graph_power, SimpleGraph.starGraph, SimpleGraph.top_adj]
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, hdist u v h⟩
