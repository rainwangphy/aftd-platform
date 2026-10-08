import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3TensorRankGe

/-!
# matrix3_tensor_rank_not_le_iff_ge_succ

Topic: algebraic_complexity   Node: fdbe469b108c

Provenance: original. Related work: folklore; generalizes matrix3_tensor_rank_not_le_22_iff_ge_23

For any commutative semiring R and any natural number r, the tensor rank of 3x3 matrix multiplication over R is not at most r if and only if every valid triad decomposition of 3x3 matrix multiplication over R has length at least r + 1.
-/

/-- For any commutative semiring R and bound r, 3x3 matrix multiplication does not have rank at most r iff its rank is at least r + 1. -/
theorem matrix3_tensor_rank_not_le_iff_ge_succ (R : Type*) [CommSemiring R] (r : ℕ) : (¬ matrix3_tensor_rank_le R r) ↔ matrix3_tensor_rank_ge R (r + 1) := by
  dsimp [matrix3_tensor_rank_le, matrix3_tensor_rank_ge]
  constructor
  · intro h L hL
    by_contra! hlt
    exact h ⟨L, by omega, hL⟩
  · intro h ⟨L, hlen, hL⟩
    have := h L hL
    omega
