import AFTD.Prelude
import AFTD.Kb.Optimization.IsConvexPolygonSlackMatrix
import AFTD.Kb.Optimization.PolygonPsdVertexCount
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# polygon_psd_vertex_count_ge_three

Topic: integer_programming   Node: d6c99ede031b

Provenance: helper lemma. arXiv:2610.04498 Sec. 2

For any natural numbers r and n, if n is the vertex count of a convex polygon admitting a size-r positive semidefinite slack factorization, then 3 ≤ n.
-/

/-- Every polygon admitting a positive semidefinite slack factorization has at least 3 vertices. -/
theorem polygon_psd_vertex_count_ge_three {r n : ℕ} (h : n ∈ polygon_psd_vertex_count r) : 3 ≤ n := by
  rcases h with ⟨S, hS, -⟩
  exact hS.1
