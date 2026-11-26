import AFTD.Prelude

/-!
# persistent_dictatorship_algebra_mult

Topic: social_choice   Node: 278ec9f9a1aa

Provenance: helper lemma. arXiv:2611.30683 Theorem 3.10 -- Stay or Switch? Metric Distortion with Online Candidate Arrivals

For any real numbers n, S0, and S1 such that 2 ≤ n and (n - 1) * S0 ≤ 3 * S1, the inequality n * S0 + 2 * S1 ≤ ((5 * n - 2) / (n + 2)) * (S0 + S1) holds.
-/

/-- Algebraic bound maximizing (n*S0 + 2*S1)/(S0 + S1) when (n-1)*S0 <= 3*S1. -/
lemma persistent_dictatorship_algebra_mult (n S₀ S₁ : ℝ) (hn : 2 ≤ n)
    (hS₀ : (n - 1) * S₀ ≤ 3 * S₁) :
    n * S₀ + 2 * S₁ ≤ ((5 * n - 2) / (n + 2)) * (S₀ + S₁) := by
  have hn2 : 0 < n + 2 := by linarith
  rw [div_mul_eq_mul_div₀, le_div_iff₀ hn2]
  nlinarith
