import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_centered_binomial_weight_bounds

Topic: statistical_mechanics   Node: 88fd776e9cff

Provenance: helper lemma. OP-892: shifted binomial kernel comparison.

Every zero-extended centered binomial weight lies between zero and one.
-/

theorem energy_filter_centered_binomial_weight_bounds (k : ℕ) (s : ℤ) :
    0 ≤ energy_filter_centered_binomial_weight k s ∧
      energy_filter_centered_binomial_weight k s ≤ 1 := by
  unfold energy_filter_centered_binomial_weight
  split_ifs with h
  · have hden : 0 < (Nat.choose (2 * k) k : ℝ) := by
      exact_mod_cast Nat.centralBinom_pos k
    constructor
    · positivity
    · apply (div_le_one hden).2
      exact_mod_cast Nat.choose_le_centralBinom (((k : ℤ) + s).toNat) k
  · simp
