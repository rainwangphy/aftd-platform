import AFTD.Prelude
import AFTD.Kb.Optimization.IsConvexPolygonSlackMatrix
import AFTD.Kb.Optimization.MatrixHasPsdFactorization
import AFTD.Kb.Optimization.PolygonPsdVertexCount
import AFTD.Kb.Optimization.PolygonV2

/-!
# polygon_v2_four_ge_eight

Topic: integer_programming   Node: cb96f6e9ce9d

Provenance: formalization of a published result. Source: arXiv:2610.04498 Thm. 7.1

If there exists a convex octagon in the plane admitting a real positive semidefinite slack factorization of size 4, and the set of realizable vertex counts is bounded above, then 8 ≤ V₂(4).
-/

/-- V₂(4) is at least 8, provided an 8-gon with size-4 PSD slack factorization exists and the vertex count is bounded above. -/
theorem polygon_v2_four_ge_eight (h8 : 8 ∈ polygon_psd_vertex_count 4) (hb : BddAbove (polygon_psd_vertex_count 4)) : 8 ≤ polygon_v2 4 := le_csSup hb h8
