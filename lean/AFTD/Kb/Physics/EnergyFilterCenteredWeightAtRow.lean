import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_centered_weight_at_row

Topic: statistical_mechanics   Node: afac2f51e8bb

Provenance: helper lemma. OP-892: binomial-row specialization of the exact trace reindexing.

For j≤2k, the centered binomial weight at j−k is choose(2k,j) divided by the central coefficient.
-/

theorem energy_filter_centered_weight_at_row (k j : ℕ) (hj : j < 2*k+1) :
    energy_filter_centered_binomial_weight k ((j:ℤ)-(k:ℤ)) =
      (Nat.choose (2*k) j : ℝ) / (Nat.choose (2*k) k : ℝ) := by
  have hr : -(k:ℤ) ≤ (j:ℤ)-(k:ℤ) ∧ (j:ℤ)-(k:ℤ) ≤ (k:ℤ) := by omega
  have hi : ((k:ℤ) + ((j:ℤ)-(k:ℤ))).toNat = j := by omega
  simp [energy_filter_centered_binomial_weight, hr, hi]
