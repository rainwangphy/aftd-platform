import AFTD.Prelude

/-!
# nonclairvoyant_scheduling_ratio_bound_of_large_index

Topic: online_algorithms   Node: fa5d39d262d2

Provenance: helper lemma. arXiv:2610.29037, Appendix C.2, Proof of Theorem 4.6 (Step 5)

For any natural number n with 2 ≤ n and any natural number s such that (n : ℝ) + 3 < 4 * (s : ℝ), the quantity ((n : ℝ) + 1) * ((n : ℝ) + 1 - (s : ℝ)) / (2 * (n : ℝ) * (s : ℝ)) is strictly less than 3 / 2.
-/

/-- For s > (n + 3) / 4, the ratio ((n + 1)(n + 1 - s)) / (2ns) is strictly less than 3/2. -/
theorem nonclairvoyant_scheduling_ratio_bound_of_large_index
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hs : (n : ℝ) + 3 < 4 * (s : ℝ)) :
    ((n : ℝ) + 1) * ((n : ℝ) + 1 - (s : ℝ)) / (2 * (n : ℝ) * (s : ℝ)) < 3 / 2 := by
  have hnR : (2 : ℝ) ≤ n := by norm_cast
  have hden : 0 < 2 * (n : ℝ) * (s : ℝ) := by
    have : 0 < (s : ℝ) := by linarith
    positivity
  rw [div_lt_iff₀ hden]
  nlinarith
