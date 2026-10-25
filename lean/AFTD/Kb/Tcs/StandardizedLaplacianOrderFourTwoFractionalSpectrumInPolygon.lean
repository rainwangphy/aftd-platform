import AFTD.Prelude
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFourMemOfIneqs
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFour
import AFTD.Kb.Tcs.IsStandardizedLaplacianTwoFractional

/-!
# standardized_laplacian_order_four_two_fractional_spectrum_in_polygon

Topic: graphs   Node: e970ab9eac72

Provenance: helper lemma. step towards op_465_standardized_laplacian_order_four_polygon_conjecture

If for every order-4 two-fractional standardized Laplacian L and every eigenvalue z of L one has |Im z| ≤ 1/4, |Im z| ≤ Re z and Re z + |Im z| ≤ 1, then every eigenvalue of every order-4 two-fractional standardized Laplacian belongs to S_4.
-/

/-- Given the three two-fractional linear spectral bounds, every eigenvalue of every order-4 two-fractional standardized Laplacian lies in S_4. -/
theorem standardized_laplacian_order_four_two_fractional_spectrum_in_polygon
    (h_im_le : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ), is_standardized_laplacian_two_fractional 4 L →
      ∀ z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), |z.im| ≤ (1 : ℝ) / 4)
    (h_left : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ), is_standardized_laplacian_two_fractional 4 L →
      ∀ z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), |z.im| ≤ z.re)
    (h_right : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ), is_standardized_laplacian_two_fractional 4 L →
      ∀ z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), z.re + |z.im| ≤ 1) :
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ), is_standardized_laplacian_two_fractional 4 L →
      ∀ z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), z ∈ standardized_laplacian_polygon_four := by
  intro L hL z hz
  exact standardized_laplacian_polygon_four_mem_of_ineqs z (h_im_le L hL z hz) (h_left L hL z hz) (h_right L hL z hz)
