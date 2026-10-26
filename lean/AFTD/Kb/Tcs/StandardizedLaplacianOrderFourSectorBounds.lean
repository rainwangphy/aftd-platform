import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShift
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShiftRowSum
import AFTD.Kb.Tcs.MatrixOrderFourCenteredShiftMulVec
import AFTD.Kb.Tcs.MatrixRowSumZeroShiftedEigenvector
import AFTD.Kb.Tcs.MatrixOrderFourMemSpectrumOfEigenpair
import AFTD.Kb.Tcs.StandardizedLaplacianOrderFourImLeRe
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_order_four_sector_bounds

Topic: graphs   Node: 3fca7e6e8db2

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

Every complex eigenvalue of an order-four standardized Laplacian satisfies both the sector inequality at zero and its reflection at one.
-/

theorem standardized_laplacian_order_four_sector_bounds (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian 4 L) (z : ℂ)
    (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ))) :
    |z.im| ≤ z.re ∧ z.re + |z.im| ≤ 1 := by
  have hleft := standardized_laplacian_order_four_im_le_re L hL z hz
  refine ⟨hleft, ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  by_cases hz1 : z = 1
  · simp [hz1]
  let K := matrix_order_four_centered_shift (-L) 1
  have hrneg : ∀ i, ∑ j, (-L) i j = 0 := by
    intro i
    simpa only [Matrix.neg_apply, Finset.sum_neg_distrib, neg_zero] using
      congrArg Neg.neg (hL.1 i)
  have hrK : ∀ i, ∑ j, K i j = 0 := matrix_order_four_centered_shift_row_sum (-L) hrneg 1
  have hK : is_standardized_laplacian 4 K := by
    refine ⟨hrK, ?_⟩
    intro i j hij
    dsimp only [K, matrix_order_four_centered_shift]
    rw [if_neg hij]
    simp only [Matrix.neg_apply]
    have hb := hL.2 i j hij
    constructor <;> linarith [hb.1, hb.2]
  have he : z ∈ spectrum ℂ (Matrix.toLin' (L.map (algebraMap ℝ ℂ))) := by
    rwa [Matrix.spectrum_toLin']
  obtain ⟨v, hve, hv0⟩ := (Module.End.HasEigenvalue.of_mem_spectrum he).exists_hasEigenvector
  have hv : (L.map (algebraMap ℝ ℂ)).mulVec v = z • v :=
    Module.End.mem_eigenspace_iff.mp hve
  have hneg : ((-L).map (algebraMap ℝ ℂ)).mulVec v = -(z • v) := by
    rw [← hv]
    ext i
    simp [Matrix.mulVec, dotProduct]
  have hKv : (K.map (algebraMap ℝ ℂ)).mulVec v =
      fun i => (1 - z) * v i - (∑ j, v j) / 4 := by
    rw [matrix_order_four_centered_shift_mulVec, hneg]
    ext i
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_one]
    ring
  obtain ⟨w, hw0, hw⟩ := matrix_row_sum_zero_shifted_eigenvector L K hL.1 hrK v hv0 z hz0 hv
    (1 - z) (-(∑ j, v j) / 4) (sub_ne_zero.mpr (Ne.symm hz1)) (by
      rw [hKv]
      ext i
      ring)
  have hright := standardized_laplacian_order_four_im_le_re K hK (1 - z) (matrix_order_four_mem_spectrum_of_eigenpair K w hw0 _ hw)
  simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, Complex.sub_re,
    Complex.one_re] at hright
  linarith
