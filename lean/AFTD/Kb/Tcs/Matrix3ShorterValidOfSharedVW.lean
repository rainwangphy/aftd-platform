import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3EvalTriadMerge

/-!
# matrix3_shorter_valid_of_shared_v_w

Topic: algebraic_complexity   Node: ddab02545db2

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

If a list of triads written as L₁ ++ t₁ :: L₂ ++ t₂ :: L₃ is a valid decomposition of matrix multiplication, and t₁ and t₂ have the same v and the same w, then there is a valid decomposition with strictly fewer triads (merging their u matrices).
-/

/-- Valid 3x3 triad decompositions can be shortened by merging two triads sharing v and w components. -/
theorem matrix3_shorter_valid_of_shared_v_w {R : Type*} [CommSemiring R]
    (L₁ L₂ L₃ : List (Matrix3Triad R)) (t₁ t₂ : Matrix3Triad R)
    (hv : t₁.v = t₂.v) (hw : t₁.w = t₂.w)
    (h : is_valid_matrix3_decomposition (L₁ ++ t₁ :: L₂ ++ t₂ :: L₃)) :
    ∃ L' : List (Matrix3Triad R),
      L'.length < (L₁ ++ t₁ :: L₂ ++ t₂ :: L₃).length ∧ is_valid_matrix3_decomposition L' := by
  refine ⟨L₁ ++ ⟨t₁.u + t₂.u, t₁.v, t₁.w⟩ :: (L₂ ++ L₃), ?_, ?_⟩
  · simp [List.length_append, List.length_cons]
  · intro A B
    have ht1 : t₁ = ⟨t₁.u, t₁.v, t₁.w⟩ := by cases t₁; rfl
    have ht2 : t₂ = ⟨t₂.u, t₁.v, t₁.w⟩ := by cases t₂; simp [hv, hw]
    have h1 : eval_matrix3_triad t₁ A B + eval_matrix3_triad t₂ A B
        = eval_matrix3_triad ⟨t₁.u + t₂.u, t₁.v, t₁.w⟩ A B := by
      rw [ht1, ht2]
      exact (matrix3_eval_triad_merge t₁.u t₂.u t₁.v t₂.v t₁.w t₂.w A B).2.1
    have hh := h A B
    rw [← hh]
    unfold eval_matrix3_decomposition
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    rw [← h1]
    ac_rfl
