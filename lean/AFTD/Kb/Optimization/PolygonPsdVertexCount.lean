import AFTD.Prelude
import AFTD.Kb.Optimization.IsConvexPolygonSlackMatrix
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# polygon_psd_vertex_count

Topic: integer_programming   Node: 0979d408fa1a

Provenance: original. Related work: arXiv:2610.04498 Sec. 1

For a natural number r, polygon_psd_vertex_count r is the set of natural numbers n such that there exists an n × n real matrix S that is the slack matrix of a convex n-gon in the plane and has a real positive semidefinite factorization of size r.
-/

/-- The set of vertex counts n of convex polygons in ℝ² admitting a size-r real positive semidefinite slack factorization. -/
def polygon_psd_vertex_count (r : ℕ) : Set ℕ := {n : ℕ | ∃ (S : Matrix (Fin n) (Fin n) ℝ), is_convex_polygon_slack_matrix n S ∧ matrix_has_psd_factorization S r}
