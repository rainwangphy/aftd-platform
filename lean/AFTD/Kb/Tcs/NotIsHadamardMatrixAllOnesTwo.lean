import AFTD.Prelude
import AFTD.Kb.Tcs.IsHadamardMatrix

/-!
# not_is_hadamard_matrix_all_ones_two

Topic: combinatorics   Node: 21cdb3cc607b

Provenance: helper lemma. sanity lemma for IsHadamardMatrix

The 2 × 2 all-ones matrix is not a Hadamard matrix.
-/

theorem not_is_hadamard_matrix_all_ones_two :
    ¬ IsHadamardMatrix (Matrix.of fun (_ _ : Fin 2) => (1 : ℤ)) := by
  rintro ⟨-, h⟩
  have := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply] at this
