import AFTD.Prelude

/-!
# matrix_trace_vecMulVec_mul_vecMulVec

Topic: integer_programming   Node: b4a75d7e8e7f

Provenance: helper lemma. arXiv:2610.04498 Lemma 2.1 proof -- Rank-sensitive vertex bounds for semidefinite lifts

For any finite type r and vectors u, v : r → ℝ, the trace of the product of outer products vecMulVec u u and vecMulVec v v equals the square of their dot product (u ⬝ᵥ v)^2.
-/

/-- The trace of the product of outer products (u uᵀ) and (v vᵀ) equals the square of the dot product u ⬝ᵥ v. -/
theorem matrix_trace_vecMulVec_mul_vecMulVec {r : Type*} [Fintype r] (u v : r → ℝ) : Matrix.trace (Matrix.vecMulVec u u * Matrix.vecMulVec v v) = (u ⬝ᵥ v) ^ 2 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul]
  ring
