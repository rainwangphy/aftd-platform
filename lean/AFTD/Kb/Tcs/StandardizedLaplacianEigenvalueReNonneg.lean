import AFTD.Prelude
import AFTD.Kb.Tcs.StandardizedLaplacianEigenvalueGershgorinDisc
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_eigenvalue_re_nonneg

Topic: graphs   Node: 110640a0f023

Provenance: helper lemma. step towards op_465_standardized_laplacian_order_four_polygon_conjecture

Every complex eigenvalue z of a standardized Laplacian matrix of order n has nonnegative real part.
-/

theorem standardized_laplacian_eigenvalue_re_nonneg (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : is_standardized_laplacian n L) (z : ℂ)
    (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ))) :
    0 ≤ z.re := by
  obtain ⟨k, hk⟩ := standardized_laplacian_eigenvalue_gershgorin_disc n L hL z hz
  have h1 : |(z - (L k k : ℂ)).re| ≤ ‖z - (L k k : ℂ)‖ := Complex.abs_re_le_norm _
  have h2 : (z - (L k k : ℂ)).re = z.re - L k k := by simp
  have h3 : - (z - (L k k : ℂ)).re ≤ |(z - (L k k : ℂ)).re| := neg_le_abs _
  linarith
