import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3UnitCheck
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# matrix3_unit_check_eq_true_iff

Topic: algebraic_complexity   Node: 0de366582283

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

The computable checker matrix3_unit_check is true exactly when the list agrees with matrix multiplication on every pair of 3x3 matrix units.
-/

/-- The Bool checker is true exactly on the lists agreeing with matrix multiplication on the 81 matrix-unit pairs; it discharges a `decide` into the hypothesis of matrix3_valid_of_unit_checks. -/
theorem matrix3_unit_check_eq_true_iff (L : List (Matrix3Triad (ZMod 2))) :
    matrix3_unit_check L = true ↔
      ∀ i j k l : Fin 3,
        eval_matrix3_decomposition L (Matrix.single i j (1 : ZMod 2)) (Matrix.single k l (1 : ZMod 2))
          = Matrix.single i j (1 : ZMod 2) * Matrix.single k l (1 : ZMod 2) := by
  simp [matrix3_unit_check, List.all_eq_true, List.mem_finRange, decide_eq_true_eq]
