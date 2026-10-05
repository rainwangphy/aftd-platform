import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseAnonymous
import AFTD.Kb.GameTheoryEconomics.FseLeftmost
import AFTD.Kb.GameTheoryEconomics.FseLeftmostLe
import AFTD.Kb.GameTheoryEconomics.FseLeftmostAttained

/-!
# fse_leftmost_anonymous

Topic: mechanism_design   Node: 0a34a7bef9e1

The leftmost mechanism is anonymous.
-/

/-- The leftmost mechanism is anonymous. -/
lemma fse_leftmost_anonymous {n : ℕ} [NeZero n] : fse_Anonymous (fse_leftmost (n := n)) := by
  intro σ x
  apply le_antisymm
  · obtain ⟨j, hj⟩ := fse_leftmost_attained x
    rw [hj]
    have := fse_leftmost_le (x ∘ σ) (σ.symm j)
    simpa using this
  · obtain ⟨j, hj⟩ := fse_leftmost_attained (x ∘ σ)
    rw [hj]
    exact fse_leftmost_le x (σ j)
