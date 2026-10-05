import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankGe

/-!
# matrix3_tensor_rank_not_le_22_iff_ge_23

Topic: algebraic_complexity   Node: 8b492c720de7

For any commutative semiring R, the tensor rank of 3x3 matrix multiplication is not at most 22 if and only if the tensor rank is at least 23.
-/

/-- Over any commutative semiring R, the tensor rank of 3x3 matrix multiplication is not at most 22 if and only if it is at least 23. -/
theorem matrix3_tensor_rank_not_le_22_iff_ge_23 (R : Type*) [CommSemiring R] : (¬ matrix3_tensor_rank_le R 22) ↔ matrix3_tensor_rank_ge R 23 := by
  unfold matrix3_tensor_rank_le matrix3_tensor_rank_ge
  constructor
  · intro h L hL
    by_contra hlt
    exact h ⟨L, by omega, hL⟩
  · rintro h ⟨L, hlen, hL⟩
    have := h L hL
    omega
