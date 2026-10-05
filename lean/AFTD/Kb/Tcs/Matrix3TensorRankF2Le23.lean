import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankLe23OfCommRing

/-!
# matrix3_tensor_rank_f2_le_23

Topic: algebraic_complexity   Node: 8dbb8364c63b

The tensor rank of 3x3 matrix multiplication over the field ZMod 2 is at most 23; that is, there exists a valid decomposition of 3x3 matrix multiplication over ZMod 2 of length at most 23.
-/

/-- The tensor rank of 3x3 matrix multiplication over the finite field F2 is at most 23. -/
theorem matrix3_tensor_rank_f2_le_23 : matrix3_tensor_rank_le (ZMod 2) 23 := matrix3_tensor_rank_le_23_of_comm_ring (ZMod 2)
