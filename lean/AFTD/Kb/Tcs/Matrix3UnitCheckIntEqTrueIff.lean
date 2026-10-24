import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3UnitCheckInt
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# matrix3_unit_check_int_eq_true_iff

Topic: algebraic_complexity   Node: 2fdb889576ed

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

The computable integer checker matrix3_unit_check_int is true if and only if the list agrees with matrix multiplication on all 81 pairs of 3x3 standard basis units.
-/

/-- The computable integer checker matrix3_unit_check_int is true if and only if the list agrees with matrix multiplication on all 81 pairs of 3x3 standard basis units. -/
theorem matrix3_unit_check_int_eq_true_iff (L : List (Matrix3Triad ℤ)) :
    matrix3_unit_check_int L = true ↔
      ∀ i j k l : Fin 3,
        eval_matrix3_decomposition L (Matrix.single i j (1 : ℤ)) (Matrix.single k l (1 : ℤ))
          = Matrix.single i j (1 : ℤ) * Matrix.single k l (1 : ℤ) := by
  simp [matrix3_unit_check_int, List.all_eq_true, List.mem_finRange, decide_eq_true_eq]
