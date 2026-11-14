import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_centered_binomial_weight_eq_natAbs

Topic: statistical_mechanics   Node: 53d3d8277c68

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

If the absolute value of integer s is at most k, the centered binomial weight equals choose(2k,k+|s|)/choose(2k,k).
-/

theorem energy_filter_centered_binomial_weight_eq_natAbs
    (k : ℕ) (s : ℤ) (hs : s.natAbs ≤ k) :
    energy_filter_centered_binomial_weight k s =
      (Nat.choose (2*k) (k+s.natAbs) : ℝ) / (Nat.choose (2*k) k : ℝ) := by
  have hrange : -(k:ℤ) ≤ s ∧ s ≤ (k:ℤ) := by omega
  simp only [energy_filter_centered_binomial_weight, if_pos hrange]
  rcases le_total 0 s with hpos | hneg
  · have hj : (s.natAbs : ℤ) = s := by simp [abs_of_nonneg hpos]
    have hidx : ((k:ℤ)+s).toNat = k+s.natAbs := by omega
    rw [hidx]
  · have hj : (s.natAbs : ℤ) = -s := by simp [abs_of_nonpos hneg]
    have hidx : ((k:ℤ)+s).toNat = k-s.natAbs := by omega
    have hsym := Nat.choose_symm (show k+s.natAbs ≤ 2*k by omega)
    have hsub : 2*k-(k+s.natAbs) = k-s.natAbs := by omega
    rw [hsub] at hsym
    rw [hidx, hsym]
