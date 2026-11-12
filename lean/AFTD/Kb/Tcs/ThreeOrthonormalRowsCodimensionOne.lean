import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# three_orthonormal_rows_codimension_one

Topic: quantum   Node: 0ed67fe5c69d

Provenance: helper lemma. Linear-algebra helper for the rank-four source in OP-693.

The complementary projection of three complex orthonormal rows in four dimensions is a rank-one projector.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
private noncomputable def in767_codimproof_codim_vector (U : Matrix (Fin 3) (Fin 4) ℂ) : Fin 4 → ℂ :=
  ![(U.submatrix id ![1,2,3]).det, -(U.submatrix id ![0,2,3]).det,
    (U.submatrix id ![0,1,3]).det, -(U.submatrix id ![0,1,2]).det]

private lemma in767_codimproof_codim_vector_kernel (U : Matrix (Fin 3) (Fin 4) ℂ) :
    U *ᵥ in767_codimproof_codim_vector U = 0 := by
  ext i
  fin_cases i <;>
    simp [in767_codimproof_codim_vector, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.det_fin_three, Matrix.submatrix_apply] <;> ring

private lemma in767_codimproof_codim_vector_norm (U : Matrix (Fin 3) (Fin 4) ℂ) :
    star (in767_codimproof_codim_vector U) ⬝ᵥ in767_codimproof_codim_vector U = (U*Uᴴ).det := by
  simp [in767_codimproof_codim_vector, dotProduct, Fin.sum_univ_four, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_add, star_sub, star_mul, Fin.sum_univ_three]
  ring

private noncomputable def in767_codimproof_completed_rows (U : Matrix (Fin 3) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![U 0, U 1, U 2, star (in767_codimproof_codim_vector U)]

private lemma in767_codimproof_completed_rows_isometry (U : Matrix (Fin 3) (Fin 4) ℂ) (hU : U*Uᴴ=1) :
    in767_codimproof_completed_rows U * (in767_codimproof_completed_rows U)ᴴ = 1 := by
  let w := in767_codimproof_codim_vector U
  have hrows (i j : Fin 3) :
      (∑ k : Fin 4, U i k * star (U j k)) = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hU
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have hker (i : Fin 3) : (∑ k : Fin 4, U i k * w k)=0 := by
    have h := congrFun (in767_codimproof_codim_vector_kernel U) i
    simpa [w,Matrix.mulVec,dotProduct] using h
  have hkerc (i : Fin 3) : (∑ k : Fin 4, star (w k) * star (U i k))=0 := by
    have h := congrArg star (hker i)
    simpa [star_sum, star_mul] using h
  have hnorm : (∑ k : Fin 4, star (w k)*w k)=1 := by
    have h := in767_codimproof_codim_vector_norm U
    rw [hU, Matrix.det_one] at h
    simpa [w, dotProduct] using h
  simp only [Fin.sum_univ_four] at hrows hker hkerc hnorm
  simp only [w, Complex.star_def] at hrows hker hkerc hnorm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [in767_codimproof_completed_rows, w, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
      Matrix.one_apply, hrows, hker, hkerc, hnorm]

private lemma in767_codimproof_codimension_one_projection (U : Matrix (Fin 3) (Fin 4) ℂ) (hU : U*Uᴴ=1) :
    ∃ w : Fin 4 → ℂ, 1-Uᴴ*U=vecMulVec w (star w) := by
  let w := in767_codimproof_codim_vector U
  let V := in767_codimproof_completed_rows U
  have hV : V*Vᴴ=1 := in767_codimproof_completed_rows_isometry U hU
  have hV' : Vᴴ*V=1 := mul_eq_one_comm.mp hV
  refine ⟨w, ?_⟩
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) hV'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] at hh
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]
  simp [V, in767_codimproof_completed_rows, w] at hh
  simp only [w, Complex.star_def] at hh ⊢
  linear_combination -hh

theorem three_orthonormal_rows_codimension_one :
  ∀ U : Matrix (Fin 3) (Fin 4) ℂ, U*Uᴴ = 1 →
    ∃ w : Fin 4 → ℂ,
      1 - Uᴴ*U = vecMulVec w (star w) := by
  intro U hU
  exact in767_codimproof_codimension_one_projection U hU
