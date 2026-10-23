import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixSupport
import AFTD.Kb.Optimization.MatrixPsdRank
import AFTD.Kb.Optimization.MatrixSupportHadamardSelf
import AFTD.Kb.Optimization.MatrixPsdRankHadamardSelfLeRank

/-!
# matrix_support_psd_rank_bound_le_rank

Topic: integer_programming   Node: 8f63e9dd7cac

Provenance: formalization of a published result. Source: scout/2610-04498-rank-sensitive-vertex-bounds-for-semidefinite-lifts.md:2048

For finite types m and n, let b : Set (m × n) → ℝ be a function on support patterns such that b (matrix_support M) ≤ (matrix_psd_rank M : ℝ) for every nonnegative real matrix M : Matrix m n ℝ. Then b (matrix_support M) ≤ (Matrix.rank M : ℝ) for every nonnegative real matrix M.
-/

/-- Any support-based lower bound for semidefinite rank cannot exceed the ordinary rank of any nonnegative matrix. -/
theorem matrix_support_psd_rank_bound_le_rank {m n : Type*} [Fintype m] [Fintype n] (b : Set (m × n) → ℝ) (h_bound : ∀ (M : Matrix m n ℝ), (∀ i j, 0 ≤ M i j) → b (matrix_support M) ≤ (matrix_psd_rank M : ℝ)) (M : Matrix m n ℝ) (hM : ∀ i j, 0 ≤ M i j) : b (matrix_support M) ≤ (Matrix.rank M : ℝ) := by
  have _ := hM
  have h_nonneg : ∀ i j, 0 ≤ Matrix.hadamard M M i j := fun i j => mul_self_nonneg (M i j)
  have h1 := h_bound (Matrix.hadamard M M) h_nonneg
  rw [matrix_support_hadamard_self] at h1
  exact h1.trans (Nat.cast_le.mpr (matrix_psd_rank_hadamard_self_le_rank M))
