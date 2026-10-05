import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_ge

Topic: algebraic_complexity   Node: a072305007d1

For a commutative semiring R and a natural number r, matrix3_tensor_rank_ge R r asserts that for every list L of elements of Matrix3Triad R, if is_valid_matrix3_decomposition L holds, then r is less than or equal to the length of L.
-/

/-- The tensor rank of 3x3 matrix multiplication over R is at least r. -/
def matrix3_tensor_rank_ge (R : Type*) [CommSemiring R] (r : ℕ) : Prop :=
  ∀ L : List (Matrix3Triad R), is_valid_matrix3_decomposition L → r ≤ L.length
