import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTriangleMatrix
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.Tcs.ComparisonTriangle
import AFTD.Kb.Tcs.ComparisonFeature2

/-!
# comparison_pi_ord

Topic: quantum   Node: 3867d33d5dca

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The real square matrix Pi_ord on comparison_feature2 n defined by Pi_ord = I - (1/3) U U^T + (1 / (3 (C(n,3) + 3))) v v^T, where U = U_triangle is the matrix of triangle relation vectors, v = U 1 is the sum of its columns, and C(n,3) is the binomial coefficient nu_triangle.
-/

/-- The real square matrix Pi_ord on comparison_feature2 n defined by Pi_ord = I - (1/3) U U^T + (1 / (3 (C(n,3) + 3))) v v^T, where U = U_triangle is the matrix of triangle relation vectors, v = U 1 is the sum of its columns, and C(n,3) is the binomial coefficient nu_triangle. -/
noncomputable def comparison_pi_ord (n : ℕ) : Matrix (comparison_feature2 n) (comparison_feature2 n) ℝ :=
  let U := comparison_triangle_matrix n
  let v := Matrix.mulVec U (fun _ => 1)
  1 - (1 / 3 : ℝ) • (U * U.transpose)
    + (1 / (3 * ((n.choose 3 : ℝ) + 3))) • Matrix.vecMulVec v v
