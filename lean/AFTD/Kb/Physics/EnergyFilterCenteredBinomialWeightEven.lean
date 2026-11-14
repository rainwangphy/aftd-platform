import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeightEqNatAbs

/-!
# energy_filter_centered_binomial_weight_even

Topic: statistical_mechanics   Node: f59f284be3c5

Provenance: helper lemma. OP-892: binomial-row specialization of the exact trace reindexing.

Every centered binomial weight is invariant under negating its integer offset.
-/

theorem energy_filter_centered_binomial_weight_even (k : ℕ) (t : ℤ) :
    energy_filter_centered_binomial_weight k (-t) = energy_filter_centered_binomial_weight k t := by
  by_cases h : t.natAbs ≤ k
  · have hn : (-t).natAbs ≤ k := by simpa using h
    rw [energy_filter_centered_binomial_weight_eq_natAbs k (-t) hn,
      energy_filter_centered_binomial_weight_eq_natAbs k t h]
    simp
  · have ht : ¬ (-(k:ℤ) ≤ t ∧ t ≤ (k:ℤ)) := by omega
    have hn : ¬ (-(k:ℤ) ≤ -t ∧ -t ≤ (k:ℤ)) := by omega
    unfold energy_filter_centered_binomial_weight
    rw [if_neg hn, if_neg ht]
