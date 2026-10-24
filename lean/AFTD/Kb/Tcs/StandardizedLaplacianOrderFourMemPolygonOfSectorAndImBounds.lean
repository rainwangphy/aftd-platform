import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFour
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFourMemOfIneqs

/-!
# standardized_laplacian_order_four_mem_polygon_of_sector_and_im_bounds

Topic: graphs   Node: 1a61f6c9214b

Provenance: original. Related work: arXiv:2610.14100 Sec. 7.3, Question 1

For any standardized Laplacian matrix L of order 4 and any complex eigenvalue z of L, if z satisfies |Im(z)| ≤ 1/4, |Im(z)| ≤ Re(z), and Re(z) + |Im(z)| ≤ 1, then z belongs to the standardized Laplacian polygon S_4.
-/

/-- An eigenvalue of an order-4 standardized Laplacian belongs to S_4 if it satisfies the sector bounds and imaginary bound. -/
theorem standardized_laplacian_order_four_mem_polygon_of_sector_and_im_bounds
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : is_standardized_laplacian 4 L)
    (z : ℂ) (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)))
    (h_im_le : |z.im| ≤ (1 : ℝ) / 4)
    (h_sector_left : |z.im| ≤ z.re)
    (h_sector_right : z.re + |z.im| ≤ 1) :
    z ∈ standardized_laplacian_polygon_four := standardized_laplacian_polygon_four_mem_of_ineqs z h_im_le h_sector_left h_sector_right
