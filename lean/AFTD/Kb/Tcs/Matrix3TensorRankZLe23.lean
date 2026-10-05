import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankLe23OfCommRing

/-!
# matrix3_tensor_rank_z_le_23

Topic: algebraic_complexity   Node: 54b76b01b168

The tensor rank of 3x3 matrix multiplication over the integers is at most 23; that is, there exists a valid decomposition of 3x3 matrix multiplication over ℤ of length at most 23.
-/

/-- The upper bound of 23 multiplications for 3x3 matrix multiplication over the integers ℤ. -/
theorem matrix3_tensor_rank_z_le_23 : matrix3_tensor_rank_le ℤ 23 := matrix3_tensor_rank_le_23_of_comm_ring ℤ
