import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3UnitCheck
import AFTD.Kb.Tcs.Matrix3UnitCheckEqTrueIff
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.Matrix3TensorRankLe23OfCommRing

/-!
# matrix3_unit_check_witnesses

Topic: algebraic_complexity   Node: c2209fc4553f

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

The checker matrix3_unit_check returns true on the classical 23-triad decomposition of 3x3 matrix multiplication over ZMod 2 (so the verification pipeline is sound end to end), and returns false on the empty list (so it does not accept everything).
-/

/-- Sanity witnesses for the checker: it returns true on the classical 23-triad algorithm and false on the empty list, so it is neither vacuously true nor vacuously false. -/
theorem matrix3_unit_check_witnesses :
    matrix3_unit_check (matrix3_triads_23 (ZMod 2)) = true ∧
      matrix3_unit_check ([] : List (Matrix3Triad (ZMod 2))) = false := ⟨(matrix3_unit_check_eq_true_iff _).2 fun _ _ _ _ => matrix3_triads_23_valid (ZMod 2) _ _, rfl⟩
