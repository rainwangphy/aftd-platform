import AFTD.Prelude
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFour

/-!
# zero_mem_standardized_laplacian_polygon_four

Topic: graphs   Node: e0a77e59ff76

Provenance: helper lemma. arXiv:2610.14100 Sec. 2

The origin zero belongs to the standardized Laplacian polygon S_4.
-/

/-- The origin zero lies in the standardized Laplacian polygon S_4. -/
theorem zero_mem_standardized_laplacian_polygon_four : (0 : ℂ) ∈ standardized_laplacian_polygon_four := by
  unfold standardized_laplacian_polygon_four
  apply subset_convexHull
  left
  use ⟨0, by decide⟩
  simp
