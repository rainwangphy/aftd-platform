import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceState
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord

/-!
# persuasion_slice_prior

Topic: mechanism_design   Node: 94acc8b1bee1

The slice prior: uniform over the 2m+1 states persuasion_slice_state m s.
-/

open Finset in
/-- The slice prior: uniform over the `2m+1` states `persuasion_slice_state m s`. -/
noncomputable def persuasion_slice_prior (m : ℕ) : (persuasion_slice_coord m → Bool) → ℝ :=
  fun x => ∑ s, if persuasion_slice_state m s = x then 1 / (2 * m + 1 : ℝ) else 0
