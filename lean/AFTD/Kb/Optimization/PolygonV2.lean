import AFTD.Prelude
import AFTD.Kb.Optimization.IsConvexPolygonSlackMatrix
import AFTD.Kb.Optimization.MatrixHasPsdFactorization
import AFTD.Kb.Optimization.PolygonPsdVertexCount

/-!
# polygon_v2

Topic: integer_programming   Node: 1c750dd23abf

Provenance: formalization of a published result. Source: arXiv:2610.04498 Sec. 1

For a natural number r, polygon_v2 r is V₂(r), defined as the supremum of the set of vertex counts of convex polygons in the plane admitting a real positive semidefinite slack factorization of size at most r.
-/

/-- The maximum number of vertices V₂(r) of a convex polygon in the plane admitting a real positive semidefinite slack factorization of size at most r. -/
noncomputable def polygon_v2 (r : ℕ) : ℕ := sSup (polygon_psd_vertex_count r)
