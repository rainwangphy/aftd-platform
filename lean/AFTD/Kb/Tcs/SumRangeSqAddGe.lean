import AFTD.Prelude

/-!
# sum_range_sq_add_ge

Topic: combinatorics   Node: 0ee2de36311f

Provenance: helper lemma. arXiv:2611.04644, Lemma A.4 proof step 2

For any natural number m and any real number t, the sum of (t + k)^2 for k from 0 to m - 1 is at least (1/12) m (m^2 - 1).
-/

lemma sum_range_sq_add_ge_eq (m : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range m, (t + (k : ℝ)) ^ 2 =
    (m : ℝ) * (t + ((m : ℝ) - 1) / 2) ^ 2 + (1 / 12 : ℝ) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The sum of squared deviations along an arithmetic progression of length m is minimized at -(m-1)/2 with value (1/12) m (m^2 - 1). -/
theorem sum_range_sq_add_ge (m : ℕ) (t : ℝ) :
    (1 / 12 : ℝ) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) ≤ ∑ k ∈ Finset.range m, (t + (k : ℝ)) ^ 2 := by
  rw [sum_range_sq_add_ge_eq]
  have h1 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 0 ≤ (t + ((m : ℝ) - 1) / 2) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (m : ℝ) * (t + ((m : ℝ) - 1) / 2) ^ 2 := mul_nonneg h1 h2
  linarith
