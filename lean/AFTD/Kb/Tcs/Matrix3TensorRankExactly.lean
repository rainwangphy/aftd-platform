import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankGe

/-!
# matrix3_tensor_rank_exactly

Topic: algebraic_complexity   Node: 0141fed726a5

For a commutative semiring R and a natural number r, matrix3_tensor_rank_exactly R r is the conjunction of matrix3_tensor_rank_le R r and matrix3_tensor_rank_ge R r.
-/

/-- The tensor rank of 3x3 matrix multiplication over R is exactly r. -/
def matrix3_tensor_rank_exactly (R : Type*) [CommSemiring R] (r : ℕ) : Prop :=
  matrix3_tensor_rank_le R r ∧ matrix3_tensor_rank_ge R r
