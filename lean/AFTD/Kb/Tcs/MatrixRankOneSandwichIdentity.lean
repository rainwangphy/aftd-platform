import AFTD.Prelude

/-!
# matrix_rank_one_sandwich_identity

Topic: computability   Node: a759d0add052

Provenance: helper lemma. arXiv:2611.06562 Appendix A

For vectors u, v and a square matrix W over a commutative ring, (u v^T) W (u v^T) = (v · (W u)) • (u v^T).
-/

/-- Rank-one sandwich identity: (u v^T) W (u v^T) = (v . W u) (u v^T). -/
theorem matrix_rank_one_sandwich_identity {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] (u v : n → R) (W : Matrix n n R) : Matrix.vecMulVec u v * W * Matrix.vecMulVec u v = (v ⬝ᵥ (Matrix.mulVec W u)) • Matrix.vecMulVec u v := by
  rw [Matrix.mul_assoc, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
