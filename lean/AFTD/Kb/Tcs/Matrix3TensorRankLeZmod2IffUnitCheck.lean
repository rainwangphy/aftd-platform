import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3UnitCheck
import AFTD.Kb.Tcs.Matrix3UnitCheckEqTrueIff
import AFTD.Kb.Tcs.Matrix3ValidOfUnitChecks
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# matrix3_tensor_rank_le_zmod2_iff_unit_check

Topic: algebraic_complexity   Node: 697ee8b9b3d8

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

For every natural number r, 3x3 matrix multiplication over ZMod 2 has a valid decomposition with at most r triads if and only if there is a list L of at most r triads over ZMod 2 whose computable unit check matrix3_unit_check L is true.
-/

/-- Over ZMod 2 the tensor-rank bound is exactly the existence of a short triad list whose computable unit check is true, i.e. the target becomes a finite Bool search over lists of at most r triads. -/
theorem matrix3_tensor_rank_le_zmod2_iff_unit_check (r : ℕ) :
    matrix3_tensor_rank_le (ZMod 2) r ↔
      ∃ L : List (Matrix3Triad (ZMod 2)), L.length ≤ r ∧ matrix3_unit_check L = true := by
  constructor
  · rintro ⟨L, hlen, hval⟩
    refine ⟨L, hlen, ?_⟩
    rw [matrix3_unit_check_eq_true_iff]
    intro i j k l
    exact hval _ _
  · rintro ⟨L, hlen, hchk⟩
    refine ⟨L, hlen, ?_⟩
    rw [matrix3_unit_check_eq_true_iff] at hchk
    exact matrix3_valid_of_unit_checks L hchk
