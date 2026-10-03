import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoupling

/-!
# persuasion_slice_scheme

Topic: mechanism_design   Node: a51b62e1e268

The optimal scheme for the slice prior.
-/

open Finset in
/-- The optimal scheme for the slice prior. -/
noncomputable def persuasion_slice_scheme (m : ℕ) :
    (persuasion_slice_coord m → Bool) → (persuasion_slice_coord m → Bool) → ℝ :=
  persuasion_pair_or_scheme (persuasion_slice_coupling m)
