import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoupling
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceState
import AFTD.Kb.GameTheoryEconomics.IsObedientDirectScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSchemeObedient
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCouplingMarginal

/-!
# persuasion_slice_scheme_obedient

Topic: mechanism_design   Node: 7c23141f4dc4

The slice scheme (pair the realised state with a uniformly random other state and recommend the coordinatewise OR) is an obedient direct scheme for the slice prior.
-/

open Finset in
/-- The slice coupling is nonnegative. -/
lemma persuasion_slice_coupling_nonneg (m : ℕ) (x y : persuasion_slice_coord m → Bool) :
    0 ≤ persuasion_slice_coupling m x y :=
  sum_nonneg fun s _ => sum_nonneg fun t _ => by split_ifs <;> positivity

open Finset in
/-- The slice coupling is symmetric. -/
lemma persuasion_slice_coupling_symm (m : ℕ) (x y : persuasion_slice_coord m → Bool) :
    persuasion_slice_coupling m x y = persuasion_slice_coupling m y x := by
  unfold persuasion_slice_coupling
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl; intro s _
  apply sum_congr rfl; intro t _
  by_cases h : s ≠ t ∧ persuasion_slice_state m s = x ∧ persuasion_slice_state m t = y
  · rw [if_pos h, if_pos ⟨Ne.symm h.1, h.2.2, h.2.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨Ne.symm h'.1, h'.2.2, h'.2.1⟩)]

open Finset in
/-- The slice scheme (pair the realised state with a uniformly random other state and recommend the coordinatewise OR) is an obedient direct scheme for the slice prior. -/
lemma persuasion_slice_scheme_obedient (m : ℕ) (hm : 1 ≤ m) :
    is_obedient_direct_scheme (persuasion_slice_prior m) (persuasion_slice_scheme m) :=
  persuasion_pair_or_scheme_obedient _ _ (persuasion_slice_coupling_nonneg m)
    (persuasion_slice_coupling_symm m) (persuasion_slice_coupling_marginal m hm)
