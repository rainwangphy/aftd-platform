import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsUniformBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtilityLe
import AFTD.Kb.GameTheoryEconomics.IsBitPrior

/-!
# persuasion_uniform_even_ratio_le_three_halves

Topic: mechanism_design   Node: cb7693985e91

Provenance: helper lemma. arXiv:2606.22226

For every natural number m, every finite type ι, and every prior μ on ι → Bool that is uniform on 2m distinct states, the maximum receiver utility R_max(μ) is at most (3/2) times the prior utility R_0(μ).
-/

open Finset in
/-- Every prior uniform on 2m states satisfies the universal 3/2 receiver utility ratio bound. -/
theorem persuasion_uniform_even_ratio_le_three_halves (m : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (μ : (ι → Bool) → ℝ)
    (hμ : is_uniform_bit_prior (2 * m) μ) :
    persuasion_max_receiver_utility μ ≤ 3 / 2 * persuasion_prior_utility μ := by
  exact persuasion_max_receiver_utility_le μ hμ.1
