import AFTD.Prelude

/-!
# nae_sin_five

Topic: quantum   Node: 06d020a62663

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For real u, sin(5u) = sin(u)(16 sin⁴(u) − 20 sin²(u) + 5).
-/

theorem nae_sin_five (u : ℝ) : Real.sin (5 * u) =
    Real.sin u * (16 * Real.sin u ^ 4 - 20 * Real.sin u ^ 2 + 5) := by
  have heq : 5 * u = 2 * u + 3 * u := by ring
  rw [heq, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul,
    Real.sin_three_mul, Real.cos_three_mul]
  linear_combination (8 * Real.sin u * (Real.cos u ^ 2 - 2 * Real.sin u ^ 2 + 1)) *
    (Real.sin_sq_add_cos_sq u)
