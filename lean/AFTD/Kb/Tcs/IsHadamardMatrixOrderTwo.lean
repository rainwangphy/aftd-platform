import AFTD.Prelude
import AFTD.Kb.Tcs.IsHadamardMatrix

/-!
# is_hadamard_matrix_order_two

Topic: combinatorics   Node: aad5345e28be

Provenance: helper lemma. sanity lemma for IsHadamardMatrix

The matrix [[1, 1], [1, -1]] is a Hadamard matrix of order 2.
-/

theorem is_hadamard_matrix_order_two : IsHadamardMatrix !![(1 : ℤ), 1; 1, -1] := by
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.one_apply]
