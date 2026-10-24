import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3UnitCheckInt
import AFTD.Kb.Tcs.Matrix3UnitCheckIntEqTrueIff
import AFTD.Kb.Tcs.Matrix3ValidOfUnitChecks
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# matrix3_tensor_rank_le_int_iff_unit_check

Topic: algebraic_complexity   Node: 57cfa2fe6366

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

The tensor rank of 3x3 matrix multiplication over ℤ is at most r if and only if there exists a list of at most r triads whose computable unit checker returns true.
-/

/-- The tensor rank of 3x3 matrix multiplication over ℤ is at most r if and only if there exists a list of at most r triads whose computable unit checker returns true. -/
theorem matrix3_tensor_rank_le_int_iff_unit_check (r : ℕ) :
    matrix3_tensor_rank_le ℤ r ↔
      ∃ L : List (Matrix3Triad ℤ), L.length ≤ r ∧ matrix3_unit_check_int L = true := by
  constructor
  · rintro ⟨L, hlen, hval⟩
    refine ⟨L, hlen, ?_⟩
    rw [matrix3_unit_check_int_eq_true_iff]
    intro i j k l
    exact hval (Matrix.single i j 1) (Matrix.single k l 1)
  · rintro ⟨L, hlen, hchk⟩
    refine ⟨L, hlen, ?_⟩
    apply matrix3_valid_of_unit_checks
    rw [← matrix3_unit_check_int_eq_true_iff]
    exact hchk
