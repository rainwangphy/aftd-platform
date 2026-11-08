import AFTD.Prelude

/-!
# oneshot_drf_bound_le_five_sqrt

Topic: online_algorithms   Node: f53954ee82c6

Provenance: helper lemma. arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Theorem 1

For every natural number D ≥ 1 and every non-negative real number opt, (4 * Real.sqrt D + 1) * opt ≤ 5 * Real.sqrt D * opt.
-/

/-- Arithmetic simplification bounding 4*sqrt(D) + 1 by 5*sqrt(D) when D ≥ 1. -/
theorem oneshot_drf_bound_le_five_sqrt (D : ℕ) (hD : 1 ≤ D) (opt : ℝ) (hopt : 0 ≤ opt) : (4 * Real.sqrt (D : ℝ) + 1) * opt ≤ 5 * Real.sqrt (D : ℝ) * opt := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (D : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hD
  have h1 : 4 * Real.sqrt (D : ℝ) + 1 ≤ 5 * Real.sqrt (D : ℝ) := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hopt
  linarith
