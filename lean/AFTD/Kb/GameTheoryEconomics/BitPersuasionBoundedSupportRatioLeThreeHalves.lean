import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtilityLe

/-!
# bit_persuasion_bounded_support_ratio_le_three_halves

Topic: mechanism_design   Node: 27ed885664e1

Provenance: helper lemma. arXiv:2606.22226

For every natural number m, every finite type ι with [DecidableEq ι], and every prior μ on ι → Bool that is a bit prior supported on at most 2m states (cardinality of {x | μ x ≠ 0} is at most 2m), persuasion_max_receiver_utility μ ≤ (3 / 2) * persuasion_prior_utility μ.
-/

open Finset in
/-- For any prior supported on at most 2m states, R_max(μ) is at most (3/2) R_0(μ). -/
theorem bit_persuasion_bounded_support_ratio_le_three_halves
    (m : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] (μ : (ι → Bool) → ℝ)
    (hμ : is_bit_prior μ) (hsupp : (univ.filter (fun x => μ x ≠ 0)).card ≤ 2 * m) :
    persuasion_max_receiver_utility μ ≤ 3 / 2 * persuasion_prior_utility μ := by first | exact persuasion_max_receiver_utility_le | (apply persuasion_max_receiver_utility_le <;> assumption) | (apply persuasion_max_receiver_utility_le <;> simp_all) | simpa using persuasion_max_receiver_utility_le | (simp only [persuasion_prior_utility, is_bit_prior, persuasion_max_receiver_utility] at *; first | exact persuasion_max_receiver_utility_le | (apply persuasion_max_receiver_utility_le <;> assumption) | (apply persuasion_max_receiver_utility_le <;> simp_all) | simpa using persuasion_max_receiver_utility_le)
