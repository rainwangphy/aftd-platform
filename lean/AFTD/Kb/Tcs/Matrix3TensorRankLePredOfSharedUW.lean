import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.Matrix3ShorterValidOfSharedUW
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_le_pred_of_shared_u_w

Topic: algebraic_complexity   Node: f56595741eaa

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

If a valid decomposition has length at most r and contains two triads sharing u and w, then the tensor rank of 3x3 matrix multiplication over R is at most r - 1.
-/

/-- Tensor rank bound decreases by at least 1 when a valid decomposition contains two triads sharing u and w. -/
theorem matrix3_tensor_rank_le_pred_of_shared_u_w {R : Type*} [CommSemiring R]
    (r : ℕ) (L₁ L₂ L₃ : List (Matrix3Triad R)) (t₁ t₂ : Matrix3Triad R)
    (hu : t₁.u = t₂.u) (hw : t₁.w = t₂.w)
    (hlen : (L₁ ++ t₁ :: L₂ ++ t₂ :: L₃).length ≤ r)
    (hval : is_valid_matrix3_decomposition (L₁ ++ t₁ :: L₂ ++ t₂ :: L₃)) :
    matrix3_tensor_rank_le R (r - 1) := by
  obtain ⟨L', hlt, hval'⟩ :=
    matrix3_shorter_valid_of_shared_u_w L₁ L₂ L₃ t₁ t₂ hu hw hval
  exact ⟨L', by omega, hval'⟩
