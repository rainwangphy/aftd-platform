import AFTD.Prelude
import AFTD.Kb.Tcs.ProperlyColorsKColorable
import AFTD.Kb.Tcs.ColorsUsed

/-!
# op869_online_coloring_clique_exact

Topic: online_algorithms   Node: 024d7d3aa622

Provenance: helper lemma. folklore

For any natural number k, any coloring algorithm A : SimpleGraph (Fin k) → (Fin k → ℕ) that properly colors k-colorable graphs uses exactly k colors on some k-colorable graph on Fin k.
-/

/-- On k vertices, any algorithm properly coloring k-colorable graphs uses exactly k colors on the complete graph. -/
theorem op869_online_coloring_clique_exact (k : ℕ)
    (A : SimpleGraph (Fin k) → (Fin k → ℕ))
    (hprop : ProperlyColorsKColorable k A) :
    ∃ G : SimpleGraph (Fin k), G.Colorable k ∧ colorsUsed (A G) = k := by
  have hcolor : (⊤ : SimpleGraph (Fin k)).Colorable k :=
    ⟨SimpleGraph.Coloring.mk id (by
      intro v w h
      exact (SimpleGraph.top_adj v w).mp h)⟩
  refine ⟨⊤, hcolor, ?_⟩
  unfold colorsUsed
  rw [Finset.card_image_of_injOn]
  · simp
  · intro u _ v _ huv
    by_contra hne
    exact hprop ⊤ hcolor u v ((SimpleGraph.top_adj u v).mpr hne) huv
