import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleTwoSidedColoringFoldCount
import AFTD.Kb.Tcs.DoubledTriangleIsoperimetricRatio
import AFTD.Kb.Tcs.DoubledTriangleFoldCount
import AFTD.Kb.Tcs.DoubledTriangleTwoSidedColoring

/-!
# doubled_triangle_two_sided_coloring_isoperimetric_ratio

Topic: combinatorics   Node: 280a18183000

Provenance: formalization of a published result. Source: arXiv:2611.12065, Proposition 3.3

For any positive integer n > 0, the Eisenstein isoperimetric ratio of the two-sided coloring B_n of T(n) is equal to 9 / 2 in Q.
-/

/-- The isoperimetric ratio eta of the two-sided coloring B_n is 9/2. -/
theorem doubled_triangle_two_sided_coloring_isoperimetric_ratio {n : ℕ} (hn : 0 < n) :
    doubled_triangle_isoperimetric_ratio n (doubled_triangle_two_sided_coloring n) = 9 / 2 := by
  rw [doubled_triangle_isoperimetric_ratio, doubled_triangle_two_sided_coloring_fold_count]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  push_cast
  field_simp
  ring
