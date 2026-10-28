import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsChordal

/-!
# is_chordal_bot

Topic: equilibria   Node: b060d86d0b20

Provenance: helper lemma. folklore

The edgeless graph on any vertex type is chordal.
-/

/-- The empty (edgeless) graph on any vertex type is chordal. -/
theorem is_chordal_bot (V : Type*) : is_chordal (⊥ : SimpleGraph V) := by
  intro n hn h
  rcases h with ⟨f⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h01 : (SimpleGraph.cycleGraph (m + 4)).Adj (0 : Fin (m + 4)) (1 : Fin (m + 4)) := by
    change ((0 : Fin (m + 4)) - 1 = 1 ∨ (1 : Fin (m + 4)) - 0 = 1)
    right
    ext
    simp
  have := (SimpleGraph.Embedding.map_adj_iff f).mpr h01
  simpa using this
