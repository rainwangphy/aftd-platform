import AFTD.Prelude

/-!
# transpose_one_add_diagonal_mul_mul

Topic: lp_duality   Node: 18495091a74f

Provenance: helper lemma. scout/2611-07815-newton-steps-are-faster-for-linear-complementarity-problems.md:529

For any finite index type n with decidable equality, any real n-by-n matrix M, and any vector d : n → ℝ, the transpose of 1 + Matrix.diagonal d * M * Matrix.diagonal d equals 1 + Matrix.diagonal d * M.transpose * Matrix.diagonal d.
-/

/-- The transpose of I_n + DMD is I_n + DMᵀD for any diagonal matrix D. -/
theorem transpose_one_add_diagonal_mul_mul {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (d : n → ℝ) :
    (1 + Matrix.diagonal d * M * Matrix.diagonal d).transpose =
      1 + Matrix.diagonal d * M.transpose * Matrix.diagonal d := by
  simp [Matrix.mul_assoc]
