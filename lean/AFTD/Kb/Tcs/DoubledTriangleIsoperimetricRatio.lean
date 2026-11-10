import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleFoldCount
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_isoperimetric_ratio

Topic: combinatorics   Node: 15e04b9989f4

Provenance: formalization of a published result. Source: arXiv:2611.12065, Definition 2.1

The Eisenstein isoperimetric ratio eta(C) of a face 2-coloring C of the doubled equilateral triangle triangulation T(n), defined as the square of the fold count of C divided by 2 * n^2, as a rational number.
-/

/-- The Eisenstein isoperimetric ratio eta of a face coloring of T(n). -/
def doubled_triangle_isoperimetric_ratio (n : ℕ) (C : DoubledTriangleFace n → Bool) : ℚ := ((doubled_triangle_fold_count C : ℚ) ^ 2) / (2 * (n : ℚ) ^ 2)
