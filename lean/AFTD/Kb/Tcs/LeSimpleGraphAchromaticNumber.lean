import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.SimpleGraphColoringIsAchromatic

/-!
# le_simple_graph_achromatic_number

Topic: graphs   Node: 76016a45f662

Provenance: helper lemma. sanity lemma for simple_graph_achromatic_number; serves OP-442

An achromatic colouring with k colours shows χ_a(G) ≥ k (the set of such k is bounded by |V| since achromatic colourings are surjective).
-/

theorem le_simple_graph_achromatic_number {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (C : G.Coloring (Fin k)) (hC : simple_graph_coloring_is_achromatic C) :
    k ≤ simple_graph_achromatic_number G := by
  dsimp [simple_graph_achromatic_number]
  apply le_csSup
  · refine ⟨Fintype.card V, ?_⟩
    rintro m ⟨Cm, hCm⟩
    have := Fintype.card_le_of_surjective (⇑Cm) hCm.1
    rw [Fintype.card_fin] at this
    exact this
  · exact ⟨C, hC⟩
