import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3ValidIffTraceTensorIdentity
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# matrix3_valid_cyclic_rotate

Topic: algebraic_complexity   Node: 4a05626b5c1d

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Cyclic rotation (u, v, w) ↦ (v, wᵀ, uᵀ) of every triad in a valid 3x3 matrix multiplication decomposition produces another valid decomposition of the same length.
-/

/-- Cyclic rotation (u, v, w) ↦ (v, wᵀ, uᵀ) of every triad in a valid 3x3 matrix multiplication decomposition produces another valid decomposition of the same length. -/
theorem matrix3_valid_cyclic_rotate {R : Type*} [CommSemiring R]
    (L : List (Matrix3Triad R)) (hL : is_valid_matrix3_decomposition L) :
    is_valid_matrix3_decomposition
      (L.map fun t => ⟨t.v, t.w.transpose, t.u.transpose⟩) := by
  let n := L.length
  let a : Fin n → Matrix (Fin 3) (Fin 3) R := fun s => (L.get s).u
  let b : Fin n → Matrix (Fin 3) (Fin 3) R := fun s => (L.get s).v
  let c : Fin n → Matrix (Fin 3) (Fin 3) R := fun s => (L.get s).w.transpose
  have hL_eq : L = List.ofFn (fun s => (⟨a s, b s, (c s).transpose⟩ : Matrix3Triad R)) := by
    nth_rw 1 [← List.ofFn_get L]
    apply congr_arg
    funext s
    simp [a, b, c]
  have h_tensor : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0 := by
    have h_valid := hL
    rw [hL_eq] at h_valid
    exact (matrix3_valid_iff_trace_tensor_identity n a b c).mp h_valid
  have h_map_eq : (L.map fun t => ⟨t.v, t.w.transpose, t.u.transpose⟩) =
      List.ofFn (fun s => (⟨b s, c s, (a s).transpose⟩ : Matrix3Triad R)) := by
    nth_rw 1 [← List.ofFn_get L]
    rw [List.map_ofFn]
    rfl
  rw [h_map_eq]
  rw [matrix3_valid_iff_trace_tensor_identity n b c a]
  intro I J J' K K' I'
  have h_orig := h_tensor K' I' I J J' K
  have h_eq : (if I' = I ∧ J = J' ∧ K' = K then (1 : R) else 0) =
              (if J = J' ∧ K = K' ∧ I = I' then (1 : R) else 0) := by
    congr 1
    simp only [eq_comm, and_comm, and_left_comm]
  rw [← h_eq, ← h_orig]
  apply Finset.sum_congr rfl
  intro s _
  ring
