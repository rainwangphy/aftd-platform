import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsMortal

/-!
# matrix_is_mortal_of_zero_mem

Topic: computability   Node: 0c28aacb19e2

Provenance: helper lemma. folklore

Any set of square matrices containing the zero matrix is mortal.
-/

/-- Any set of matrices containing the zero matrix is mortal. -/
theorem matrix_is_mortal_of_zero_mem {m : Type*} [Fintype m] [DecidableEq m] {α : Type*} [Semiring α] {S : Set (Matrix m m α)} (h0 : 0 ∈ S) : matrix_is_mortal S := ⟨[0], by simp, by simp [h0], by simp⟩
