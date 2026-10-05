import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.EvalMatrix3DecompositionApply
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_le_of_surjective

Topic: algebraic_complexity   Node: 9f47e6980f17

If f : R → S is a surjective homomorphism of commutative semirings and 3x3 matrix multiplication over R has a valid triad decomposition with at most r products, then so does 3x3 matrix multiplication over S (apply f to every coefficient).
-/

/-- The image of a triad under a ring homomorphism, entrywise. -/
def matrix3_triad_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (t : Matrix3Triad R) : Matrix3Triad S :=
  ⟨t.u.map f, t.v.map f, t.w.map f⟩

/-- Evaluating a decomposition commutes with applying a ring homomorphism. -/
theorem eval_matrix3_decomposition_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (L : List (Matrix3Triad R)) (A B : Matrix (Fin 3) (Fin 3) R) :
    (eval_matrix3_decomposition L A B).map f =
      eval_matrix3_decomposition (L.map (matrix3_triad_map f)) (A.map f) (B.map f) := by
  ext i j
  rw [Matrix.map_apply, eval_matrix3_decomposition_apply, eval_matrix3_decomposition_apply,
    map_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [matrix3_triad_map, map_sum, map_mul]

/-- A valid decomposition stays valid under a surjective ring homomorphism. -/
theorem is_valid_matrix3_decomposition_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Surjective f) (L : List (Matrix3Triad R))
    (hL : is_valid_matrix3_decomposition L) :
    is_valid_matrix3_decomposition (L.map (matrix3_triad_map f)) := by
  intro A' B'
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin 3) (Fin 3) R, A.map f = A' :=
    ⟨fun i j => (hf (A' i j)).choose, by ext i j; exact (hf (A' i j)).choose_spec⟩
  obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin 3) (Fin 3) R, B.map f = B' :=
    ⟨fun i j => (hf (B' i j)).choose, by ext i j; exact (hf (B' i j)).choose_spec⟩
  rw [← eval_matrix3_decomposition_map, hL A B, Matrix.map_mul]

theorem matrix3_tensor_rank_le_of_surjective {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (hf : Function.Surjective f) (r : ℕ) (h : matrix3_tensor_rank_le R r) : matrix3_tensor_rank_le S r := by
  obtain ⟨L, hlen, hL⟩ := h
  exact ⟨L.map (matrix3_triad_map f), by simpa using hlen, is_valid_matrix3_decomposition_map f hf L hL⟩
