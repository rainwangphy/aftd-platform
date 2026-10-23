import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixSupport

/-!
# matrix_support_hadamard_self

Topic: integer_programming   Node: d5195debe6a2

Provenance: helper lemma. scout/2610-04498-rank-sensitive-vertex-bounds-for-semidefinite-lifts.md:2056

For any real matrix M, the Hadamard square M ∘ M has the same support as M.
-/

/-- The Hadamard square of a real matrix has the same support as the matrix itself. -/
theorem matrix_support_hadamard_self {m n : Type*} (M : Matrix m n ℝ) : matrix_support (Matrix.hadamard M M) = matrix_support M := by
  ext ⟨i, j⟩
  simp [matrix_support, Matrix.hadamard_apply]
