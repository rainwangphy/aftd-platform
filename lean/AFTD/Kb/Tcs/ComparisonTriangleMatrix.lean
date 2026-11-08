import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTriangleKappa
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonTriangle

/-!
# comparison_triangle_matrix

Topic: quantum   Node: 98e87bc8e495

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The real matrix U_triangle with rows indexed by comparison_feature2 n and columns by triangles, whose column at the triangle t is the triangle relation vector kappa_t.
-/

/-- The real matrix U_triangle with rows indexed by comparison_feature2 n and columns by triangles, whose column at the triangle t is the triangle relation vector kappa_t. -/
def comparison_triangle_matrix (n : ℕ) : Matrix (comparison_feature2 n) (comparison_triangle n) ℝ :=
  Matrix.of fun i t => comparison_triangle_kappa t i
