import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankGe
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankExactly
import AFTD.Kb.Tcs.Matrix3TensorRankNotLe22IffGe23

/-!
# matrix3_tensor_rank_z_dichotomy

Topic: algebraic_complexity   Node: 84c2f78d02d0

Assuming that the tensor rank of 3x3 matrix multiplication over the integers is at least 22 and at most 23, the tensor rank over ℤ is either exactly 22 or exactly 23.
-/

/-- Dichotomy for the tensor rank of 3x3 matrix multiplication over ℤ: given bounds 22 and 23, the rank is either exactly 22 or exactly 23. -/
theorem matrix3_tensor_rank_z_dichotomy (h_ge : matrix3_tensor_rank_ge ℤ 22) (h_le : matrix3_tensor_rank_le ℤ 23) : matrix3_tensor_rank_exactly ℤ 22 ∨ matrix3_tensor_rank_exactly ℤ 23 := by
  by_cases h : matrix3_tensor_rank_le ℤ 22
  · exact Or.inl ⟨h, h_ge⟩
  · exact Or.inr ⟨h_le, (matrix3_tensor_rank_not_le_22_iff_ge_23 ℤ).1 h⟩
