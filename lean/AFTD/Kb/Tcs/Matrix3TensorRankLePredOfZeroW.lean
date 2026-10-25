import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.Matrix3EvalTriadZeroW
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# matrix3_tensor_rank_le_pred_of_zero_w

Topic: algebraic_complexity   Node: 3cec0d6f87f0

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

If a valid decomposition has length at most r and contains a triad with zero w matrix, then the tensor rank of 3x3 matrix multiplication over R is at most r - 1.
-/

/-- If a valid decomposition has length at most r and contains a triad with zero w matrix, then the tensor rank of 3x3 matrix multiplication over R is at most r - 1. -/
theorem matrix3_tensor_rank_le_pred_of_zero_w {R : Type*} [CommSemiring R]
    (r : ℕ) (L₁ L₂ : List (Matrix3Triad R)) (t : Matrix3Triad R)
    (hw : t.w = 0)
    (hlen : (L₁ ++ t :: L₂).length ≤ r)
    (hval : is_valid_matrix3_decomposition (L₁ ++ t :: L₂)) :
    matrix3_tensor_rank_le R (r - 1) := by
  rcases t with ⟨u, v, w⟩
  simp only at hw
  subst hw
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  · intro A B
    have key : eval_matrix3_decomposition (L₁ ++ L₂) A B
        = eval_matrix3_decomposition (L₁ ++ Matrix3Triad.mk u v 0 :: L₂) A B := by
      simp only [eval_matrix3_decomposition, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, matrix3_eval_triad_zero_w, zero_add]
    rw [key]
    exact hval A B
