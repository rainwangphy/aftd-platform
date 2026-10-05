import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankGe
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankExactly
import AFTD.Kb.Tcs.Matrix3TensorRankNotLe22IffGe23

/-!
# matrix3_tensor_rank_f2_dichotomy

Topic: algebraic_complexity   Node: 87ca95b59652

Assuming that the tensor rank of 3x3 matrix multiplication over ZMod 2 is at least 22 and at most 23, the tensor rank over ZMod 2 is either exactly 22 or exactly 23.
-/

/-- If the tensor rank of 3x3 matrix multiplication over ZMod 2 is at least 22 and at most 23, then it is either exactly 22 or exactly 23. -/
theorem matrix3_tensor_rank_f2_dichotomy (h_ge : matrix3_tensor_rank_ge (ZMod 2) 22) (h_le : matrix3_tensor_rank_le (ZMod 2) 23) : matrix3_tensor_rank_exactly (ZMod 2) 22 ∨ matrix3_tensor_rank_exactly (ZMod 2) 23 := by
  by_cases h : matrix3_tensor_rank_le (ZMod 2) 22
  · exact Or.inl ⟨h, h_ge⟩
  · exact Or.inr ⟨h_le, (matrix3_tensor_rank_not_le_22_iff_ge_23 (ZMod 2)).1 h⟩
