import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian
import AFTD.Kb.Tcs.LaplacianOrderFourStationaryEigenvalueSector
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShift
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShiftRowSum
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShiftMulVec
import AFTD.Kb.Tcs.MatrixRowSumZeroShiftedEigenvector
import AFTD.Kb.Tcs.StandardizedLaplacianOrderFourPerturbationStationary
import AFTD.Kb.Tcs.StandardizedLaplacianEigenvalueReNonneg

/-!
# standardized_laplacian_order_four_im_le_re

Topic: graphs   Node: c926f74e85d6

Provenance: helper lemma. step towards standardized_laplacian_order_four_polygon_conjecture

For any standardized Laplacian matrix L of order 4, the imaginary part and real part of every complex eigenvalue z of L satisfy |Im(z)| ≤ Re(z).
-/

/-- For any standardized Laplacian matrix L of order 4, the imaginary and real parts of every eigenvalue z satisfy |Im(z)| ≤ Re(z). -/
theorem standardized_laplacian_order_four_im_le_re (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian 4 L)
    (z : ℂ) (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ))) :
    |z.im| ≤ z.re := by
  have hzre := standardized_laplacian_eigenvalue_re_nonneg 4 L hL z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  have he : z ∈ spectrum ℂ (Matrix.toLin' (L.map (algebraMap ℝ ℂ))) := by
    rwa [Matrix.spectrum_toLin']
  obtain ⟨v, hve, hv0⟩ := (Module.End.HasEigenvalue.of_mem_spectrum he).exists_hasEigenvector
  have hv : (L.map (algebraMap ℝ ℂ)).mulVec v = z • v :=
    Module.End.mem_eigenspace_iff.mp hve
  apply le_of_forall_pos_le_add
  intro δ hδ
  let K := matrix_order_four_centered_shift L δ
  have hrK : ∀ i, ∑ j, K i j = 0 := matrix_order_four_centered_shift_row_sum L hL.1 δ
  have hoK : ∀ i j, i ≠ j → K i j ≤ 0 := by
    intro i j hij
    dsimp only [K, matrix_order_four_centered_shift]
    rw [if_neg hij]
    linarith [(hL.2 i j hij).2]
  obtain ⟨π, hπ, hstat⟩ := standardized_laplacian_order_four_perturbation_stationary L hL δ hδ
  have hlam : z + (δ : ℂ) ≠ 0 := by
    intro hh
    have hre := congrArg Complex.re hh
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  have hKv : (K.map (algebraMap ℝ ℂ)).mulVec v =
      fun i => (z + (δ : ℂ)) * v i - (δ : ℂ) / 4 * ∑ j, v j := by
    rw [matrix_order_four_centered_shift_mulVec, hv]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨w, hw0, hw⟩ := matrix_row_sum_zero_shifted_eigenvector L K hL.1 hrK v hv0 z hz0 hv
    (z + (δ : ℂ)) (-(δ : ℂ) / 4 * ∑ j, v j) hlam (by
      rw [hKv]
      ext i
      ring)
  have hb := laplacian_order_four_stationary_eigenvalue_sector K π hπ hrK hoK hstat w hw0
    (z + (δ : ℂ)) hw
  simpa only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, add_zero] using hb
