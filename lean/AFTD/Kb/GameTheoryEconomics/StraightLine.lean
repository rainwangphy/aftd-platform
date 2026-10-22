import AFTD.Prelude

/-!
# StraightLine

Topic: fair_division   Node: 67b43b45877e

Provenance: formalization of a published result. Source: arXiv:2610.27956 Section 1.1

A straight line in the plane ℝ², given by an affine functional with nonzero linear part.
-/

/-- A straight line in ℝ², represented by an affine map to ℝ with nonzero linear part. -/
structure StraightLine where
  cut : (ℝ × ℝ) →ᵃ[ℝ] ℝ
  linear_ne_zero : cut.linear ≠ 0
