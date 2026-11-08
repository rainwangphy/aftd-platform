import AFTD.Prelude

/-!
# drf_geometric_mean_bound

Topic: online_algorithms   Node: 6439cf0c39b8

Provenance: helper lemma. arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Section 3.1.5

For any natural number D, non-negative real opt, real values A, B, and Z1 with 0 ≤ A, A ≤ 2 * D * opt, B ≤ 8 * opt, and Z1^2 ≤ A * B, it holds that Z1 ≤ 4 * Real.sqrt D * opt.
-/

/-- Geometric mean bound on congestion delay combining capacity and bottleneck bounds. -/
theorem drf_geometric_mean_bound (D : ℕ) (opt A B Z1 : ℝ) (hopt : 0 ≤ opt) (hA : A ≤ 2 * (D : ℝ) * opt) (hB : B ≤ 8 * opt) (hA_nonneg : 0 ≤ A) (hCS : Z1 ^ 2 ≤ A * B) : Z1 ≤ 4 * Real.sqrt (D : ℝ) * opt := by
  have hAB1 : A * B ≤ A * (8 * opt) := mul_le_mul_of_nonneg_left hB hA_nonneg
  have hAB2 : A * (8 * opt) ≤ (2 * (D : ℝ) * opt) * (8 * opt) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have hAB : Z1 ^ 2 ≤ (4 * Real.sqrt (D : ℝ) * opt) ^ 2 := by
    have hsq : (4 * Real.sqrt (D : ℝ) * opt) ^ 2 = 16 * (D : ℝ) * opt ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg D)]
      ring
    rw [hsq]
    nlinarith
  have hnonneg : 0 ≤ 4 * Real.sqrt (D : ℝ) * opt := by positivity
  have habs : |Z1| ≤ 4 * Real.sqrt (D : ℝ) * opt := abs_le_of_sq_le_sq hAB hnonneg
  linarith [le_abs_self Z1]
