import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacianTwoFractional
import AFTD.Kb.Tcs.StandardizedLaplacianEigenvalueReNonneg
import AFTD.Kb.Tcs.StandardizedLaplacianOrderFourSectorBounds
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_order_four_two_fractional_sector

Topic: graphs   Node: fab39fb561a2

Provenance: helper lemma. step towards op_465_standardized_laplacian_order_four_polygon_conjecture

For an order-4 two-fractional standardized Laplacian, every complex eigenvalue satisfies the sector bound |Im z| ≤ Re z, and dually Re z + |Im z| ≤ 1.
-/

theorem standardized_laplacian_order_four_two_fractional_sector (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian_two_fractional 4 L) (z : ℂ)
    (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ))) :
    |z.im| ≤ z.re ∧ z.re + |z.im| ≤ 1 := by
  exact standardized_laplacian_order_four_sector_bounds L hL.1 z hz
