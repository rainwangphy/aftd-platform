import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixSupport

/-!
# matrix_support_zero

Topic: integer_programming   Node: fac05d829aca

Provenance: helper lemma. folklore

The support of the zero matrix is the empty set.
-/

/-- The support of the zero matrix is empty. -/
theorem matrix_support_zero {m n α : Type*} [Zero α] : matrix_support (0 : Matrix m n α) = ∅ := by
  simp [matrix_support]
