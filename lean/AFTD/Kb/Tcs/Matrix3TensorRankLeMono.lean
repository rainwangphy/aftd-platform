import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# matrix3_tensor_rank_le_mono

Topic: algebraic_complexity   Node: dd827f996f0c

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

For any commutative semiring R and natural numbers r₁ and r₂, if 3x3 matrix multiplication over R has tensor rank at most r₁ and r₁ ≤ r₂, then it has tensor rank at most r₂.
-/

/-- Tensor rank upper bounds for 3x3 matrix multiplication are monotonic: if the rank is at most r₁ and r₁ ≤ r₂, then the rank is at most r₂. -/
theorem matrix3_tensor_rank_le_mono {R : Type*} [CommSemiring R] {r₁ r₂ : ℕ} (h : matrix3_tensor_rank_le R r₁) (hle : r₁ ≤ r₂) : matrix3_tensor_rank_le R r₂ := by
  rcases h with ⟨L, hlen, hvalid⟩
  exact ⟨L, hlen.trans hle, hvalid⟩
