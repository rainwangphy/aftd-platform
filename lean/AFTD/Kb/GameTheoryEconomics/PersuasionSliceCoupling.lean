import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceState

/-!
# persuasion_slice_coupling

Topic: mechanism_design   Node: fb8470edd508

The coupling that pairs the realised state with a uniformly random different state.
-/

open Finset in
/-- The coupling that pairs the realised state with a uniformly random different state. -/
noncomputable def persuasion_slice_coupling (m : ℕ) :
    (persuasion_slice_coord m → Bool) → (persuasion_slice_coord m → Bool) → ℝ :=
  fun x y => ∑ s, ∑ t, if s ≠ t ∧ persuasion_slice_state m s = x ∧ persuasion_slice_state m t = y
    then 1 / ((2 * m + 1 : ℝ) * (2 * m)) else 0
