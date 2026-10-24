import AFTD.Prelude
import AFTD.Kb.Optimization.IsConvexPolygonSlackMatrix
import AFTD.Kb.Optimization.PolygonPsdVertexCountGeThree
import AFTD.Kb.Optimization.PolygonPsdVertexCount

/-!
# zero_not_mem_polygon_psd_vertex_count

Topic: integer_programming   Node: 1c20a3a7240a

Provenance: helper lemma. arXiv:2610.04498 Sec. 2

For any natural number r, 0 does not belong to the set of vertex counts of convex polygons admitting a size-r positive semidefinite slack factorization.
-/

/-- Zero is not the vertex count of any convex polygon admitting a positive semidefinite slack factorization. -/
theorem zero_not_mem_polygon_psd_vertex_count (r : ℕ) : 0 ∉ polygon_psd_vertex_count r := by
  intro h
  have := polygon_psd_vertex_count_ge_three h
  omega
