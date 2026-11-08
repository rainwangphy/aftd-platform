import AFTD.Prelude
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition

/-!
# matrix3_valid_transpose_swap

Topic: algebraic_complexity   Node: 77bc713e4975

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Transposing and swapping the two input factors along with transposing the output factor, (u, v, w) ↦ (vᵀ, uᵀ, wᵀ), preserves the validity of a 3x3 matrix multiplication decomposition.
-/

/-- Transposing and swapping the two input factors along with transposing the output factor, (u, v, w) ↦ (vᵀ, uᵀ, wᵀ), preserves the validity of a 3x3 matrix multiplication decomposition. -/
theorem matrix3_valid_transpose_swap {R : Type*} [CommSemiring R]
    (L : List (Matrix3Triad R)) (hL : is_valid_matrix3_decomposition L) :
    is_valid_matrix3_decomposition
      (L.map fun t => ⟨t.v.transpose, t.u.transpose, t.w.transpose⟩) := by
  intro A B
  unfold eval_matrix3_decomposition
  rw [List.map_map]
  have h_triad : ((fun t => eval_matrix3_triad t A B) ∘
        fun t : Matrix3Triad R => (⟨t.v.transpose, t.u.transpose, t.w.transpose⟩ : Matrix3Triad R)) =
      (Matrix.transpose ∘ fun t => eval_matrix3_triad t B.transpose A.transpose) := by
    funext t
    dsimp [eval_matrix3_triad, Matrix.transpose]
    congr 1
    have h1 : (∑ i : Fin 3, ∑ j : Fin 3, t.v j i * A i j) = (∑ i : Fin 3, ∑ j : Fin 3, t.v i j * A j i) := by
      rw [Finset.sum_comm]
    have h2 : (∑ i : Fin 3, ∑ j : Fin 3, t.u j i * B i j) = (∑ i : Fin 3, ∑ j : Fin 3, t.u i j * B j i) := by
      rw [Finset.sum_comm]
    rw [h1, h2, mul_comm]
  rw [h_triad]
  rw [← List.map_map]
  rw [← Matrix.transpose_list_sum]
  change (eval_matrix3_decomposition L B.transpose A.transpose).transpose = A * B
  rw [hL B.transpose A.transpose]
  rw [Matrix.transpose_mul]
  rw [Matrix.transpose_transpose, Matrix.transpose_transpose]
