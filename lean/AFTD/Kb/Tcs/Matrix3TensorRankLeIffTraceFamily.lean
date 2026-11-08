import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3ValidIffTraceTensorIdentity
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_le_iff_trace_family

Topic: algebraic_complexity   Node: 82be4052b93b

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

The tensor rank of 3x3 matrix multiplication over a commutative semiring R is at most r if and only if there exists a cyclic trace family of length at most r satisfying the matrix multiplication tensor coefficient identities.
-/

/-- The tensor rank of 3x3 matrix multiplication over a commutative semiring R is at most r if and only if there exists a cyclic trace family of length at most r satisfying the tensor coefficient identities. -/
theorem matrix3_tensor_rank_le_iff_trace_family {R : Type*} [CommSemiring R] (r : ℕ) :
    matrix3_tensor_rank_le R r ↔
      ∃ (n : ℕ) (_ : n ≤ r) (a b c : Fin n → Matrix (Fin 3) (Fin 3) R),
        ∀ i j j' k k' i' : Fin 3,
          ∑ s, a s i j * b s j' k * c s k' i' =
            if j = j' ∧ k = k' ∧ i = i' then 1 else 0 := by
  constructor
  · rintro ⟨L, hlen, hvalid⟩
    refine ⟨L.length, hlen, fun s => (L.get s).u, fun s => (L.get s).v, fun s => (L.get s).w.transpose, ?_⟩
    have heq : (List.ofFn fun s => ({ u := (L.get s).u, v := (L.get s).v, w := (L.get s).w.transpose.transpose } : Matrix3Triad R)) = L := by
      have : (fun s => ({ u := (L.get s).u, v := (L.get s).v, w := (L.get s).w.transpose.transpose } : Matrix3Triad R)) = L.get := by
        funext s
        simp
      rw [this, List.ofFn_get]
    rw [← matrix3_valid_iff_trace_tensor_identity]
    rwa [heq]
  · rintro ⟨n, hlen, a, b, c, hid⟩
    refine ⟨List.ofFn fun s => { u := a s, v := b s, w := (c s).transpose }, ?_, ?_⟩
    · rw [List.length_ofFn]
      exact hlen
    · exact (matrix3_valid_iff_trace_tensor_identity n a b c).mpr hid
