import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePrior
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePriorIsBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceRatio

/-!
# persuasion_receiver_ratio_sharp

Topic: mechanism_design   Node: b7c090676f88

The 3/2 bound of Yachbes–Tardos is sharp. For every c < 3/2 there is a prior with R_max(μ) > c · R_0(μ).
-/

open Finset in
/-- **The `3/2` bound of Yachbes–Tardos is sharp.** For every `c < 3/2` there is a prior with
`R_max(μ) > c · R_0(μ)`. -/
theorem persuasion_receiver_ratio_sharp (c : ℝ) (hc : c < 3 / 2) :
    ∃ m : ℕ, 1 ≤ m ∧ is_bit_prior (persuasion_slice_prior m) ∧
      c * persuasion_prior_utility (persuasion_slice_prior m) <
        persuasion_max_receiver_utility (persuasion_slice_prior m) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (3 / 2 - c))
  refine ⟨N + 1, by omega, persuasion_slice_prior_is_bit_prior _, ?_⟩
  obtain ⟨h1, h2⟩ := persuasion_slice_ratio (N + 1) (by omega)
  set R := persuasion_max_receiver_utility (persuasion_slice_prior (N + 1))
  set R0 := persuasion_prior_utility (persuasion_slice_prior (N + 1))
  have hd : 0 < 3 / 2 - c := by linarith
  have hN' : 1 < (3 / 2 - c) * N := by
    rw [div_lt_iff₀ hd] at hN; linarith
  push_cast at h1
  have hR : R = (3 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1 + 1)) * R0 := by
    field_simp; linarith
  rw [hR]
  have : c < (3 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1 + 1)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  exact mul_lt_mul_of_pos_right this h2
