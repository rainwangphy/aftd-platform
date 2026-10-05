import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankGe
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankExactly

/-!
# matrix3_tensor_rank_z_22_exact

Topic: algebraic_complexity   Node: 80d633fa9d7c

Assuming that the tensor rank of 3x3 matrix multiplication over the integers is at least 22 and at most 22, the tensor rank over ℤ is exactly 22.
-/

/-- If the tensor rank of 3x3 matrix multiplication over ℤ is both at least 22 and at most 22, it is exactly 22. -/
theorem matrix3_tensor_rank_z_22_exact (h_ge : matrix3_tensor_rank_ge ℤ 22) (h_le : matrix3_tensor_rank_le ℤ 22) : matrix3_tensor_rank_exactly ℤ 22 := ⟨h_le, h_ge⟩
