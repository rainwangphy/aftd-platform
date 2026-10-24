import AFTD.Prelude
import AFTD.Kb.Optimization.IsConvexPolygonSlackMatrix
import AFTD.Kb.Optimization.MatrixHasPsdFactorization
import AFTD.Kb.Optimization.PolygonPsdVertexCount
import AFTD.Kb.Optimization.PolygonV2

/-!
# polygon_v2_four_eq_eight_iff_no_larger

Topic: integer_programming   Node: a1e0d2908411

Provenance: original. Related work: arXiv:2610.04498 Sec. 8, P3

Assuming an 8-gon with size-4 positive semidefinite slack factorization exists and the set of realizable vertex counts is bounded above, V₂(4) = 8 if and only if every convex polygon admitting a size-4 positive semidefinite slack factorization has at most 8 vertices.
-/

/-- Characterisation of V₂(4) = 8: given attainment of 8 and boundedness, V₂(4) = 8 if and only if every realizable polygon has at most 8 vertices. -/
theorem polygon_v2_four_eq_eight_iff_no_larger (h8 : 8 ∈ polygon_psd_vertex_count 4) (hb : BddAbove (polygon_psd_vertex_count 4)) : polygon_v2 4 = 8 ↔ (∀ n ∈ polygon_psd_vertex_count 4, n ≤ 8) := by
  have hne : (polygon_psd_vertex_count 4).Nonempty := ⟨8, h8⟩
  have hge : 8 ≤ polygon_v2 4 := le_csSup hb h8
  rw [polygon_v2] at *
  rw [le_antisymm_iff]
  simp [hge, csSup_le_iff hb hne]
