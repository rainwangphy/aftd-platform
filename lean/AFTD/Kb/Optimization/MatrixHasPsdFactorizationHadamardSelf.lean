import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixHasPsdFactorization
import AFTD.Kb.Optimization.MatrixTraceVecMulVecMulVecMulVec

/-!
# matrix_has_psd_factorization_hadamard_self

Topic: integer_programming   Node: 05010dfe0dd5

Provenance: helper lemma. arXiv:2610.04498 Lemma 2.1 proof -- Rank-sensitive vertex bounds for semidefinite lifts

For finite types m and n and any real matrix R : Matrix m n ℝ, the Hadamard square Matrix.hadamard R R has a positive semidefinite factorization of size Matrix.rank R.
-/

/-- The entrywise Hadamard square R ⊙ R of a real matrix R has a positive semidefinite factorization of size rank R. -/
theorem matrix_has_psd_factorization_hadamard_self {m n : Type*} [Fintype m] [Fintype n] (R : Matrix m n ℝ) : matrix_has_psd_factorization (Matrix.hadamard R R) (Matrix.rank R) := by
  classical
  dsimp [matrix_has_psd_factorization]
  let r := Matrix.rank R
  let b : Module.Basis (Fin r) ℝ R.mulVecLin.range :=
    Module.finBasisOfFinrankEq ℝ R.mulVecLin.range rfl
  have hj (j : n) : (fun i => R i j) ∈ R.mulVecLin.range := ⟨Pi.single j 1, Matrix.mulVec_single_one R j⟩
  let U : Matrix m (Fin r) ℝ := fun i k => (b k : m → ℝ) i
  let V : Matrix (Fin r) n ℝ := fun k j => b.repr ⟨fun i => R i j, hj j⟩ k
  have hR : R = U * V := by
    ext i j
    have h := Module.Basis.sum_repr b ⟨fun i => R i j, hj j⟩
    have h_val := congr_arg Subtype.val h
    have h_eval := congr_fun h_val i
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h_eval
    rw [Matrix.mul_apply]
    rw [← h_eval]
    apply Finset.sum_congr rfl
    intro k _
    simp [U, V, mul_comm]
  let A (i : m) : Matrix (Fin r) (Fin r) ℝ := Matrix.vecMulVec (U i) (U i)
  let B (j : n) : Matrix (Fin r) (Fin r) ℝ := Matrix.vecMulVec (fun k => V k j) (fun k => V k j)
  refine ⟨A, B, ?_, ?_, ?_⟩
  · intro i
    have := Matrix.posSemidef_vecMulVec_self_star (U i)
    rwa [star_trivial] at this
  · intro j
    have := Matrix.posSemidef_vecMulVec_self_star (fun k => V k j)
    rwa [star_trivial] at this
  · intro i j
    have h_tr : (A i * B j).trace = ((U i) ⬝ᵥ (fun k => V k j)) ^ 2 := by
      dsimp [A, B]
      rw [matrix_trace_vecMulVec_mul_vecMulVec]
    rw [h_tr]
    have h_dot : (U i) ⬝ᵥ (fun k => V k j) = R i j := by
      rw [congr_fun (congr_fun hR i) j]
      rw [Matrix.mul_apply]
      rfl
    rw [h_dot]
    ring
