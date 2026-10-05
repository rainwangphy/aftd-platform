import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_le

Topic: algebraic_complexity   Node: 2c40f7c037d0

For a commutative semiring R and a natural number r, matrix3_tensor_rank_le R r asserts that there exists a list L of elements of Matrix3Triad R with length at most r such that is_valid_matrix3_decomposition L holds.
-/

/-- The tensor rank of 3x3 matrix multiplication over R is at most r. -/
def matrix3_tensor_rank_le (R : Type*) [CommSemiring R] (r : ℕ) : Prop :=
  ∃ L : List (Matrix3Triad R), L.length ≤ r ∧ is_valid_matrix3_decomposition L
