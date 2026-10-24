import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3UnitCheckInt
import AFTD.Kb.Tcs.Matrix3UnitCheckIntEqTrueIff
import AFTD.Kb.Tcs.Matrix3TensorRankLe23OfCommRing
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# matrix3_unit_check_int_witnesses

Topic: algebraic_complexity   Node: e586cf9794d2

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

The checker matrix3_unit_check_int returns true on the classical 23-triad integer decomposition and false on the empty list.
-/

/-- The checker matrix3_unit_check_int returns true on the classical 23-triad integer decomposition and false on the empty list. -/
theorem matrix3_unit_check_int_witnesses :
    matrix3_unit_check_int (matrix3_triads_23 ℤ) = true ∧
      matrix3_unit_check_int ([] : List (Matrix3Triad ℤ)) = false := by
  constructor
  · rw [matrix3_unit_check_int_eq_true_iff]
    intro i j k l
    exact matrix3_triads_23_valid ℤ _ _
  · decide
