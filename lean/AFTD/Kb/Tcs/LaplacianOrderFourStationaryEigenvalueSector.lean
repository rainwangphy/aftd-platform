import AFTD.Prelude
import AFTD.Kb.Tcs.LaplacianOrderFourStationaryEigenvalueOneSide

/-!
# laplacian_order_four_stationary_eigenvalue_sector

Topic: graphs   Node: 2a2d51bbed37

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

For a real order-four matrix with zero row sums, nonpositive off-diagonal entries, and a strictly positive left null vector, every complex eigenvalue satisfies the sector inequality.
-/

theorem laplacian_order_four_stationary_eigenvalue_sector
    (L : Matrix (Fin 4) (Fin 4) ℝ) (π : Fin 4 → ℝ)
    (hπ : ∀ i, 0 < π i)
    (hr : ∀ i, ∑ j, L i j = 0)
    (ho : ∀ i j, i ≠ j → L i j ≤ 0)
    (hs : ∀ j, ∑ i, π i * L i j = 0)
    (v : Fin 4 → ℂ) (hv0 : v ≠ 0) (z : ℂ)
    (hv : (L.map (algebraMap ℝ ℂ)).mulVec v = z • v) :
    |z.im| ≤ z.re := by
  have hp := laplacian_order_four_stationary_eigenvalue_one_side L π hπ hr ho hs v hv0 z hv
  have hvc : (L.map (algebraMap ℝ ℂ)).mulVec (star v) = (star z) • (star v) := by
    ext i
    have h := congrArg star (congrFun hv i)
    simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using h
  have hm := laplacian_order_four_stationary_eigenvalue_one_side L π hπ hr ho hs (star v)
    (by simpa using hv0) (star z) hvc
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩
