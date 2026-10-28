import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsChordal

/-!
# not_is_chordal_cycle_four

Topic: equilibria   Node: bdf06fd76cd2

Provenance: helper lemma. folklore

The cycle graph C_4 on four vertices is not chordal.
-/

/-- The 4-cycle graph C_4 is not chordal. -/
theorem not_is_chordal_cycle_four : ¬ is_chordal (SimpleGraph.cycleGraph 4) := by
  intro h
  exact h 4 le_rfl ⟨SimpleGraph.Embedding.refl⟩
