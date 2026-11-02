import AFTD.Prelude
import AFTD.Kb.Tcs.HelicalPoint

/-!
# helical_dist_sq

Topic: combinatorics   Node: e6438d153607

Provenance: helper lemma. arXiv:2610.38368, Section 2

For any natural number n and indices i, j : Fin n, the squared Euclidean distance dist (helical_point n i) (helical_point n j) ^ 2 in EuclideanSpace ℝ (Fin 3) equals 2 - 2 * Real.cos (((|((i : ℝ) - (j : ℝ))|) : ℝ) / n) + 4 * (((|((i : ℝ) - (j : ℝ))|) : ℝ) / n) ^ 2.
-/

/-- The squared distance between helical points P_i and P_j depends only on |i - j|. -/
theorem helical_dist_sq (n : ℕ) (i j : Fin n) :
    dist (helical_point n i) (helical_point n j) ^ 2 =
      2 - 2 * Real.cos (((|((i : ℝ) - (j : ℝ))|) : ℝ) / n) +
        4 * (((|((i : ℝ) - (j : ℝ))|) : ℝ) / n) ^ 2 := by
  have hdist : dist (helical_point n i) (helical_point n j) ^ 2 =
      (Real.cos ((i : ℝ) / n) - Real.cos ((j : ℝ) / n)) ^ 2 +
      (Real.sin ((i : ℝ) / n) - Real.sin ((j : ℝ) / n)) ^ 2 +
      (2 * (i : ℝ) / n - 2 * (j : ℝ) / n) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
    dsimp [helical_point]
    simp [Real.dist_eq]
  have hcos : Real.cos (((|((i : ℝ) - (j : ℝ))|) : ℝ) / n) = Real.cos ((i : ℝ) / n - (j : ℝ) / n) := by
    rw [← sub_div]
    rcases le_total 0 ((i : ℝ) - (j : ℝ)) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_div, Real.cos_neg]
  have hsq : (((|((i : ℝ) - (j : ℝ))|) : ℝ) / n) ^ 2 = ((i : ℝ) / n - (j : ℝ) / n) ^ 2 := by
    rw [← sub_div, div_pow, div_pow, sq_abs]
  rw [hdist, hcos, hsq]
  set u : ℝ := (i : ℝ) / n
  set v : ℝ := (j : ℝ) / n
  have h1 : (Real.cos u - Real.cos v) ^ 2 + (Real.sin u - Real.sin v) ^ 2 =
      2 - 2 * Real.cos (u - v) := by
    rw [Real.cos_sub]
    have h2 := Real.cos_sq_add_sin_sq u
    have h3 := Real.cos_sq_add_sin_sq v
    linear_combination h2 + h3
  have h4 : (2 * u - 2 * v) ^ 2 = 4 * (u - v) ^ 2 := by
    ring
  have h5 : (2 * (i : ℝ) / n - 2 * (j : ℝ) / n) = 2 * u - 2 * v := by
    dsimp [u, v]
    ring
  rw [h5, h4, h1]
