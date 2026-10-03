import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtilityLe
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverRatioSharp

/-!
# persuasion_receiver_ratio_optimal_constant

Topic: mechanism_design   Node: 1ddac72a70e3

The optimal constant is 3/2. 3/2 is the least c with R_max(μ) ≤ c R_0(μ) for all priors μ (over all finite coordinate sets).
-/

open Finset in
/-- **The optimal constant is `3/2`.** `3/2` is the least `c` with `R_max(μ) ≤ c R_0(μ)` for
all priors `μ` (over all finite coordinate sets). -/
theorem persuasion_receiver_ratio_optimal_constant :
    IsLeast {c : ℝ | ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (μ : (ι → Bool) → ℝ),
      is_bit_prior μ → persuasion_max_receiver_utility μ ≤ c * persuasion_prior_utility μ}
      (3 / 2) := by
  refine ⟨fun ι _ _ μ hμ => persuasion_max_receiver_utility_le μ hμ, fun c hc => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨m, -, hμ, hlt⟩ := persuasion_receiver_ratio_sharp c h
  exact absurd (hc _ _ hμ) (not_le.mpr hlt)
