import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixPermanentFromBlocksZeroOneTwo

/-!
# matrix_permanent_from_blocks_anti_diagonal

Topic: algebraic_complexity   Node: 6f808efa37ef

Provenance: formalization of a published result. Source: Minc, Permanents (1978), Chapter 2; Valiant, Completeness classes in algebra (1979)

For any commutative semiring R, any finite type n with decidable equality, and any square matrices B and C of size n x n over R, the permanent of the block matrix with 0 in the top-left block, B in the top-right block, C in the bottom-left block, and 0 in the bottom-right block equals the product of the permanent of B and the permanent of C: (Matrix.fromBlocks (0 : Matrix n n R) B C 0).permanent = B.permanent * C.permanent.
-/

/-- The permanent of a block anti-diagonal matrix with square blocks equals the product of the permanents of the off-diagonal blocks. -/
theorem matrix_permanent_from_blocks_anti_diagonal {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommSemiring R] (B C : Matrix n n R) :
    (Matrix.fromBlocks (0 : Matrix n n R) B C 0).permanent = B.permanent * C.permanent := by
  have h1 : (Matrix.fromBlocks (0 : Matrix n n R) B C 0).permanent =
      ((Matrix.fromBlocks (0 : Matrix n n R) B C 0).submatrix (Equiv.sumComm n n) id).permanent := by
    rw [Matrix.permanent_permute_cols (Equiv.sumComm n n)]
  have h2 : (Matrix.fromBlocks (0 : Matrix n n R) B C 0).submatrix (Equiv.sumComm n n) id =
      Matrix.fromBlocks C 0 0 B := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  rw [h1, h2, matrix_permanent_from_blocks_zero_one_two, mul_comm]
