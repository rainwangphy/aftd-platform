import AFTD.Prelude

/-!
# sq_sub_one_add_one_ge_sq_div_two

Topic: combinatorics   Node: 316e2afc30ad

Provenance: helper lemma. arXiv:2611.19312, Section 4, equation (1852)

For every real number a, (a - 1)^2 + 1 is at least a^2 / 2.
-/

/-- Quadratic lower bound (a - 1)^2 + 1 ≥ a^2 / 2. -/
theorem sq_sub_one_add_one_ge_sq_div_two (a : ℝ) :
    (a^2) / 2 ≤ (a - 1)^2 + 1 := by
  have h : 0 ≤ (a - 2)^2 := sq_nonneg (a - 2)
  linarith
