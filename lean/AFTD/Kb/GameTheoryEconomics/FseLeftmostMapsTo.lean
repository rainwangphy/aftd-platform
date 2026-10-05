import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseMapsToDomain
import AFTD.Kb.GameTheoryEconomics.FseLeftmost
import AFTD.Kb.GameTheoryEconomics.FseLeftmostAttained

/-!
# fse_leftmost_mapsTo

Topic: mechanism_design   Node: 527f5f63a878

The leftmost mechanism maps [0,1]^n into [0,1].
-/

/-- The leftmost mechanism maps `[0,1]^n` into `[0,1]`. -/
lemma fse_leftmost_mapsTo {n : ℕ} [NeZero n] : fse_MapsToDomain (fse_leftmost (n := n)) := by
  intro x hx
  obtain ⟨j, hj⟩ := fse_leftmost_attained x
  rw [hj]; exact hx j
