import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialGaussianPositiveOffset

/-!
# energy_filter_centered_binomial_weight_gaussian_bound

Topic: statistical_mechanics   Node: 55abc92c52ac

Provenance: helper lemma. OP-892: zero-extended centered binomial estimates.

For every k≥1 and integer s, the zero-extended centered binomial weight at s is at most exp(−s²/(2k)).
-/

theorem energy_filter_centered_binomial_weight_gaussian_bound
    (k : ℕ) (s : ℤ) (hk : 1 ≤ k) :
    energy_filter_centered_binomial_weight k s ≤
      Real.exp (-((s : ℝ)^2 / (2*(k:ℝ)))) := by
  unfold energy_filter_centered_binomial_weight
  split_ifs with hs
  · rcases le_total 0 s with hpos | hneg
    · let j := s.toNat
      have hjint : (j:ℤ) = s := Int.toNat_of_nonneg hpos
      have hjk : j ≤ k := by omega
      have hindex : ((k:ℤ)+s).toNat = k+j := by omega
      have hjreal : (j:ℝ) = (s:ℝ) := by exact_mod_cast hjint
      rw [hindex, ← hjreal]
      exact energy_filter_centered_binomial_gaussian_positive_offset k j hk hjk
    · let j := (-s).toNat
      have hjint : (j:ℤ) = -s := Int.toNat_of_nonneg (neg_nonneg.mpr hneg)
      have hjk : j ≤ k := by omega
      have hindex : ((k:ℤ)+s).toNat = k-j := by omega
      have hsym := Nat.choose_symm (show k+j ≤ 2*k by omega)
      have hsub : 2*k-(k+j) = k-j := by omega
      rw [hsub] at hsym
      have hjreal : (j:ℝ) = -(s:ℝ) := by exact_mod_cast hjint
      have hsq : (j:ℝ)^2 = (s:ℝ)^2 := by rw [hjreal]; ring
      rw [hindex, hsym, ← hsq]
      exact energy_filter_centered_binomial_gaussian_positive_offset k j hk hjk
  · exact le_of_lt (Real.exp_pos _)
