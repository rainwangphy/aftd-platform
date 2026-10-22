import AFTD.Prelude

/-!
# real_multiplicative_defect_deletion_contraction_le

Topic: combinatorics   Node: 930b59af9981

Provenance: helper lemma. arXiv:2610.27706 Lemma 5.2

Let a_D, a_star_D, t_D, a_Q, a_star_Q, t_Q be non-negative real numbers. If t_D ^ 2 ≤ a_D * a_star_D and t_Q ^ 2 ≤ a_Q * a_star_Q, then (t_D + t_Q) ^ 2 ≤ (a_D + a_Q) * (a_star_D + a_star_Q).
-/

/-- AM-GM inequality step: non-negative real numbers satisfying multiplicative defect bounds preserve the bound under addition. -/
theorem real_multiplicative_defect_deletion_contraction_le
    {a_D a_star_D t_D a_Q a_star_Q t_Q : ℝ}
    (ha_D : 0 ≤ a_D) (ha_star_D : 0 ≤ a_star_D) (ht_D : 0 ≤ t_D)
    (ha_Q : 0 ≤ a_Q) (ha_star_Q : 0 ≤ a_star_Q) (ht_Q : 0 ≤ t_Q)
    (hD : t_D ^ 2 ≤ a_D * a_star_D) (hQ : t_Q ^ 2 ≤ a_Q * a_star_Q) :
    (t_D + t_Q) ^ 2 ≤ (a_D + a_Q) * (a_star_D + a_star_Q) := by
  have h1 : (2 * t_D * t_Q) ^ 2 ≤ 4 * (a_D * a_star_D) * (a_Q * a_star_Q) := by
    nlinarith
  have h2 : 4 * (a_D * a_star_D) * (a_Q * a_star_Q) ≤ (a_D * a_star_Q + a_Q * a_star_D) ^ 2 := by
    have : 0 ≤ (a_D * a_star_Q - a_Q * a_star_D) ^ 2 := sq_nonneg _
    linarith
  have h_sq : (2 * t_D * t_Q) ^ 2 ≤ (a_D * a_star_Q + a_Q * a_star_D) ^ 2 := by
    linarith
  have h_cross_nonneg : 0 ≤ 2 * t_D * t_Q := by positivity
  have h_sum_nonneg : 0 ≤ a_D * a_star_Q + a_Q * a_star_D := by positivity
  have h_cross : 2 * t_D * t_Q ≤ a_D * a_star_Q + a_Q * a_star_D := by
    rw [sq_le_sq, abs_of_nonneg h_cross_nonneg, abs_of_nonneg h_sum_nonneg] at h_sq
    exact h_sq
  linarith
