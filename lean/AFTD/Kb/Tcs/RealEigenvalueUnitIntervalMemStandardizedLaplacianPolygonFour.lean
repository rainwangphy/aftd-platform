import AFTD.Prelude
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFour
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFourMemOfIneqs

/-!
# real_eigenvalue_unit_interval_mem_standardized_laplacian_polygon_four

Topic: graphs   Node: 7ee6e9365f7b

Provenance: original. Related work: arXiv:2610.14100 Sec. 2

Any real number x in the unit interval [0, 1], viewed as a complex number, belongs to the standardized Laplacian polygon S_4.
-/

/-- Every real number in [0, 1] belongs to the standardized Laplacian polygon S_4. -/
theorem real_eigenvalue_unit_interval_mem_standardized_laplacian_polygon_four
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (x : ℂ) ∈ standardized_laplacian_polygon_four := by
  apply standardized_laplacian_polygon_four_mem_of_ineqs <;> simp [hx0, hx1]
