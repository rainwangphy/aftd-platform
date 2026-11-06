import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsMortal

/-!
# matrix_not_is_mortal_empty

Topic: computability   Node: b75f809416ed

Provenance: helper lemma. folklore

The empty set of square matrices is not mortal.
-/

/-- The empty set of matrices is not mortal. -/
theorem matrix_not_is_mortal_empty {m : Type*} [Fintype m] [DecidableEq m] {α : Type*} [Semiring α] : ¬ matrix_is_mortal (∅ : Set (Matrix m m α)) := by
  rintro ⟨_ | ⟨x, xs⟩, hne, hmem, -⟩
  · exact hne rfl
  · exact hmem x (.head xs)
