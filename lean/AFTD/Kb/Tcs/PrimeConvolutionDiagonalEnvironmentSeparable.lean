import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsSeparable
import AFTD.Kb.Tcs.PrimeConvolutionFiveTwoFifthEntanglementBreakingIff
import AFTD.Kb.Tcs.PrimeConvolutionChoi

/-!
# prime_convolution_diagonal_environment_separable

Topic: quantum   Node: 457086326e96

Provenance: helper lemma. OP-2466 diagonal remainder of the product-orbit certificate

For any finite dimension at least two and any coupling, a convolution channel with a nonnegative diagonal environment has a separable Choi matrix.
-/

open Fin.CommRing
set_option maxHeartbeats 1000000

def in1249_basis (n : ℕ) (k : Fin (n+2)) (j : Fin (n+2)) : ℝ := if j=k then 1 else 0

theorem in1249_basis_orbit (n : ℕ) (r k j l : Fin (n+2)) :
    (∑ i, in1249_basis n 0 i * in1249_basis n k (r*i+j) *
      in1249_basis n 0 (i+j-l) * in1249_basis n k (r*(i+j-l)+l)) =
      in1249_basis n k j * in1249_basis n k l := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp only [in1249_basis, if_pos rfl, zero_mul, zero_add, one_mul]
    by_cases h : j = l
    · subst l
      simp [in1249_basis]
    · have hsub : j-l ≠ 0 := sub_ne_zero.mpr h
      simp [in1249_basis, h, hsub]; aesop
  · intro i _ hi
    simp [in1249_basis, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem in1249_basis_choi_sep (n : ℕ) (r k : Fin (n+2)) :
    matrix_is_separable (n+2) (n+2)
      (prime_convolution_choi (n+2) r (Matrix.of fun j l => (in1249_basis n k j * in1249_basis n k l : ℂ))) := by
  have h := in1243_twirl_sep n r (in1249_basis n 0) (in1249_basis n k)
  convert h using 1
  congr 1
  ext j l
  simp only [Matrix.of_apply, ← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : ℂ)) (in1249_basis_orbit n r k j l).symm

theorem prime_convolution_diagonal_environment_separable (n : ℕ) (r : Fin (n+2)) (w : Fin (n+2) → ℝ)
    (hw : ∀ j, 0 ≤ w j) :
    matrix_is_separable (n+2) (n+2)
      (prime_convolution_choi (n+2) r (Matrix.diagonal (fun j => (w j : ℂ)))) := by
  classical
  let D : Fin (n+2) → Matrix (Fin (n+2)) (Fin (n+2)) ℂ :=
    fun k => Matrix.of fun j l => (in1249_basis n k j * in1249_basis n k l : ℂ)
  have heq : Matrix.diagonal (fun j => (w j : ℂ)) = ∑ k ∈ Finset.univ, (w k : ℂ) • D k := by
    ext j l
    simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, D, Matrix.of_apply,
      in1249_basis]
    by_cases h : j = l
    · subst l
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hj
        have : j ≠ k := Ne.symm hj
        simp [this]
      · simp
    · simp only [apply_ite (fun a : ℝ => (a : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]
      rw [Finset.sum_eq_zero]
      · simp [h]
      · intro k _
        by_cases hj : j=k <;> by_cases hl : l=k <;> simp_all
  rw [heq, in1243_choi_linear (n+2) (r : ZMod (n+2)) Finset.univ w D]
  apply in1243_sep_sum
  intro k _
  exact in1243_sep_smul _ _ _ (hw k) _ (in1249_basis_choi_sep n r k)
