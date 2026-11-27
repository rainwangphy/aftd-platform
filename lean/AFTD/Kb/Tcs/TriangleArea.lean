import AFTD.Prelude

/-!
# triangle_area

Topic: combinatorics   Node: 499deb1f6da6

Provenance: formalization of a published result. Source: arXiv:2611.33233, Section 1

The area of the triangle in the plane with vertices p, q, and r is half the absolute value of (q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1).
-/

/-- The Euclidean area of the triangle formed by three points in ℝ². -/
noncomputable def triangle_area (p q r : Fin 2 → ℝ) : ℝ := (1 / 2 : ℝ) * |(q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1)|
