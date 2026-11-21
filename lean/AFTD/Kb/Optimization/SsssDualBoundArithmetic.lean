import AFTD.Prelude

/-!
# ssss_dual_bound_arithmetic

Topic: lp_duality   Node: 05901a0de1c1

Provenance: helper lemma. arXiv:2611.26188, Lemma 3.5

Let k, kp, ε, A', Y', LP be real numbers with 0 < k, 1/k < ε, k ≤ kp, (1 + ε)k - 1 ≤ kp, and 0 ≤ Y'. If k A' + 2 Y' ≤ LP and 0 ≤ kp A' + 2 Y', then 2 Y' ≤ ((1 + ε)k / (ε k - 1)) * LP.
-/

/-- Real arithmetic bound underlying the dual variable sum bound in multi-path TSP LP augmentation. -/
theorem ssss_dual_bound_arithmetic
    (k kp ε A' Y' LP : ℝ)
    (hk : 0 < k)
    (hε : 1 / k < ε)
    (hkp_ge_k : k ≤ kp)
    (hkp_bound : (1 + ε) * k - 1 ≤ kp)
    (hY : 0 ≤ Y')
    (hdual_k : k * A' + 2 * Y' ≤ LP)
    (hdual_kp : 0 ≤ kp * A' + 2 * Y') :
    2 * Y' ≤ ((1 + ε) * k / (ε * k - 1)) * LP := by
  have _ := hkp_ge_k
  have hε_pos : 0 < ε * k - 1 := by
    have : 1 < ε * k := (div_lt_iff₀ hk).mp hε
    linarith
  have hkp_diff : 0 < kp - k := by
    have : (1 + ε) * k - 1 = k + (ε * k - 1) := by ring
    linarith
  have hkp_pos : 0 < kp := by linarith
  have h1 : 0 ≤ LP - (k * A' + 2 * Y') := by linarith
  have h2 : 0 ≤ kp * (LP - (k * A' + 2 * Y')) := mul_nonneg (le_of_lt hkp_pos) h1
  have h3 : 0 ≤ k * (kp * A' + 2 * Y') := mul_nonneg (le_of_lt hk) hdual_kp
  have h4 : kp * (LP - (k * A' + 2 * Y')) + k * (kp * A' + 2 * Y') = kp * LP - (kp - k) * (2 * Y') := by ring
  have h_comb : (kp - k) * (2 * Y') ≤ kp * LP := by linarith
  have hLP : 0 ≤ LP := by
    have hy : 0 ≤ (kp - k) * (2 * Y') := mul_nonneg (le_of_lt hkp_diff) (by linarith)
    have : 0 ≤ kp * LP := by linarith
    exact nonneg_of_mul_nonneg_right this hkp_pos
  have h_step1 : 2 * Y' ≤ (kp / (kp - k)) * LP := by
    have h_comb' : 2 * Y' * (kp - k) ≤ kp * LP := by linarith
    have h_div : 2 * Y' ≤ (kp * LP) / (kp - k) := (le_div_iff₀ hkp_diff).mpr h_comb'
    have : (kp * LP) / (kp - k) = (kp / (kp - k)) * LP := by ring
    linarith
  have h_frac : kp / (kp - k) ≤ (1 + ε) * k / (ε * k - 1) := by
    have hk1 : 0 ≤ k + 1 := by linarith
    have hnum1 : kp * (k + 1) - (1 + ε) * k^2 = (1 + ε) * k * (kp - k) - kp * (ε * k - 1) := by ring
    have hnum2 : ((1 + ε) * k - 1) * (k + 1) - (1 + ε) * k^2 = ε * k - 1 := by ring
    have hnum3 : ((1 + ε) * k - 1) * (k + 1) ≤ kp * (k + 1) := mul_le_mul_of_nonneg_right hkp_bound hk1
    have h_cross : kp * (ε * k - 1) ≤ (1 + ε) * k * (kp - k) := by linarith
    rw [div_le_div_iff₀ hkp_diff hε_pos]
    exact h_cross
  have h_step2 : (kp / (kp - k)) * LP ≤ ((1 + ε) * k / (ε * k - 1)) * LP :=
    mul_le_mul_of_nonneg_right h_frac hLP
  exact le_trans h_step1 h_step2
