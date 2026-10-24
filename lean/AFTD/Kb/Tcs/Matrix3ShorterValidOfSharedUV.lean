import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3EvalTriadMerge
import AFTD.Kb.Tcs.Matrix3ShorterValidOfSharedUW

/-!
# matrix3_shorter_valid_of_shared_u_v

Topic: algebraic_complexity   Node: 8c42ac14e2a7

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

If a list of triads written as L₁ ++ t₁ :: L₂ ++ t₂ :: L₃ is a valid decomposition of matrix multiplication, and t₁ and t₂ have the same u and the same v, then there is a valid decomposition with strictly fewer triads (merging their w matrices).
-/

/-- Valid 3x3 triad decompositions can be shortened by merging two triads sharing u and v components. -/
theorem matrix3_shorter_valid_of_shared_u_v {R : Type*} [CommSemiring R]
    (L₁ L₂ L₃ : List (Matrix3Triad R)) (t₁ t₂ : Matrix3Triad R)
    (hu : t₁.u = t₂.u) (hv : t₁.v = t₂.v)
    (h : is_valid_matrix3_decomposition (L₁ ++ t₁ :: L₂ ++ t₂ :: L₃)) :
    ∃ L' : List (Matrix3Triad R),
      L'.length < (L₁ ++ t₁ :: L₂ ++ t₂ :: L₃).length ∧ is_valid_matrix3_decomposition L' := by
  refine ⟨L₁ ++ ⟨t₁.u, t₁.v, t₁.w + t₂.w⟩ :: (L₂ ++ L₃), by simp, ?_⟩
  intro A B
  have hmerge : eval_matrix3_triad t₁ A B + eval_matrix3_triad t₂ A B =
      eval_matrix3_triad ⟨t₁.u, t₁.v, t₁.w + t₂.w⟩ A B := by
    have := (matrix3_eval_triad_merge t₁.u t₂.u t₁.v t₂.v t₁.w t₂.w A B).2.2
    cases t₁
    cases t₂
    dsimp at hu hv ⊢
    subst hu hv
    exact this
  simp only [eval_matrix3_decomposition, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons]
  rw [← hmerge]
  have h_orig : eval_matrix3_decomposition (L₁ ++ t₁ :: L₂ ++ t₂ :: L₃) A B = A * B := h A B
  simp only [eval_matrix3_decomposition, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons] at h_orig
  rw [← h_orig]
  abel
