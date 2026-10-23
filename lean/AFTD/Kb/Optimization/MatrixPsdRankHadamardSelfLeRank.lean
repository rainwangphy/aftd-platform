import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixPsdRank
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# matrix_psd_rank_hadamard_self_le_rank

Topic: integer_programming   Node: 32ac27b6de3f

Provenance: helper lemma. scout/2610-04498-rank-sensitive-vertex-bounds-for-semidefinite-lifts.md:368

For finite types m and n and any real matrix M : Matrix m n ℝ, the positive semidefinite rank of the Hadamard square M ∘ M is at most the ordinary rank of M.
-/

/-- The positive semidefinite rank of the Hadamard square of a real matrix is at most its ordinary rank. -/
theorem matrix_psd_rank_hadamard_self_le_rank {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : matrix_psd_rank (Matrix.hadamard M M) ≤ Matrix.rank M := by
  classical
  apply Nat.sInf_le
  change matrix_has_psd_factorization (Matrix.hadamard M M) (Matrix.rank M)
  dsimp [matrix_has_psd_factorization]
  let r := Matrix.rank M
  let b : Module.Basis (Fin r) ℝ M.mulVecLin.range :=
    Module.finBasisOfFinrankEq ℝ M.mulVecLin.range rfl
  have hj (j : n) : (fun i => M i j) ∈ M.mulVecLin.range := ⟨Pi.single j 1, Matrix.mulVec_single_one M j⟩
  let U : Matrix m (Fin r) ℝ := fun i k => (b k : m → ℝ) i
  let V : Matrix (Fin r) n ℝ := fun k j => b.repr ⟨fun i => M i j, hj j⟩ k
  have hM : M = U * V := by
    ext i j
    have h := Module.Basis.sum_repr b ⟨fun i => M i j, hj j⟩
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
      rw [Matrix.vecMulVec_mul_vecMulVec]
      rw [Matrix.trace_vecMulVec]
      rw [dotProduct_smul]
      ring
    rw [h_tr]
    have h_dot : (U i) ⬝ᵥ (fun k => V k j) = M i j := by
      rw [congr_fun (congr_fun hM i) j]
      rw [Matrix.mul_apply]
      rfl
    rw [h_dot]
    ring
