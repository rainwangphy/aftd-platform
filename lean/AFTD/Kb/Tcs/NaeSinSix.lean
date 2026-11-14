import AFTD.Prelude

/-!
# nae_sin_six

Topic: quantum   Node: 38176c4fbfb9

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For real u, sin(6u) = 2 sin(u) cos(u)(3−4 sin²(u))(1−4 sin²(u)).
-/

theorem nae_sin_six (u : ℝ) : Real.sin (6 * u) =
    2 * Real.sin u * Real.cos u * (3 - 4 * Real.sin u ^ 2) * (1 - 4 * Real.sin u ^ 2) := by
  have heq : 6 * u = 2 * (3 * u) := by ring
  rw [heq, Real.sin_two_mul, Real.sin_three_mul, Real.cos_three_mul]
  linear_combination (8 * Real.sin u * Real.cos u * (3 - 4 * Real.sin u ^ 2)) *
    (Real.sin_sq_add_cos_sq u)
