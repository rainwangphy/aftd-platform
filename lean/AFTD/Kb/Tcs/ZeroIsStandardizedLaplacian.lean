import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# zero_is_standardized_laplacian

Topic: graphs   Node: 42bbebb52ccd

Provenance: helper lemma. folklore

For any natural number n, the n by n zero matrix is a standardized Laplacian matrix of order n.
-/

/-- The zero matrix of size n x n is a standardized Laplacian matrix. -/
theorem zero_is_standardized_laplacian (n : ℕ) :
    is_standardized_laplacian n (0 : Matrix (Fin n) (Fin n) ℝ) := by
  constructor
  · intro i
    simp
  · intro i j hij
    constructor
    · simpa using
        div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1 : ℝ) ≤ 0) (Nat.cast_nonneg n)
    · simp
