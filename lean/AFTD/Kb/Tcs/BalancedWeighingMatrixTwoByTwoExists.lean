import AFTD.Prelude
import AFTD.Kb.Tcs.IsBalancedWeighingMatrix

/-!
# balanced_weighing_matrix_two_by_two_exists

Topic: combinatorics   Node: 66df2955b072

Provenance: helper lemma. arXiv:2611.17855

There exists a balanced weighing matrix of order 2 with parameters k = 2 and λ = 2.
-/

/-- Witness that a balanced weighing matrix of order 2 with k = 2 and λ = 2 exists. -/
theorem balanced_weighing_matrix_two_by_two_exists :
    ∃ W : Matrix (Fin 2) (Fin 2) ℤ, is_balanced_weighing_matrix 2 W 2 2 := by
  use !![1, 1; 1, -1]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
