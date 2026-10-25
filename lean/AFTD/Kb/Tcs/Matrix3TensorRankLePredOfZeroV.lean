import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.Matrix3EvalTriadZeroV
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# matrix3_tensor_rank_le_pred_of_zero_v

Topic: algebraic_complexity   Node: d2987842c77f

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

If a valid decomposition has length at most r and contains a triad with zero v matrix, then the tensor rank of 3x3 matrix multiplication over R is at most r - 1.
-/

/-- If a valid decomposition has length at most r and contains a triad with zero v matrix, then the tensor rank of 3x3 matrix multiplication over R is at most r - 1. -/
theorem matrix3_tensor_rank_le_pred_of_zero_v {R : Type*} [CommSemiring R]
    (r : ℕ) (L₁ L₂ : List (Matrix3Triad R)) (t : Matrix3Triad R)
    (hv : t.v = 0)
    (hlen : (L₁ ++ t :: L₂).length ≤ r)
    (hval : is_valid_matrix3_decomposition (L₁ ++ t :: L₂)) :
    matrix3_tensor_rank_le R (r - 1) := by
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  · intro A B
    have h := hval A B
    simp only [eval_matrix3_decomposition, List.map_append,
      List.map_cons, List.sum_cons, List.sum_append] at h ⊢
    have hzero : eval_matrix3_triad t A B = 0 := by
      cases t with
      | mk u v w =>
        simp only at hv
        subst v
        exact matrix3_eval_triad_zero_v u w A B
    rw [hzero] at h
    simpa using h
