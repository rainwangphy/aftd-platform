import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3ValidIffTraceTensorIdentity
import AFTD.Kb.Tcs.Matrix3TensorRankGe
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_ge_iff_trace_tensor_bound

Topic: algebraic_complexity   Node: 8549e93917ba

Provenance: helper lemma. Adapter for OP-2 / matrix3_tensor_rank_zmod2_le_22; cyclic trace coefficient convention in arXiv:2610.11823v3, Section 2 and its companion RootSound/Tensor.lean. Proof written here using the existing unit-check extension theorem; no external proof is assumed.

A lower bound r for the lengths of all valid 3x3 matrix multiplication triad lists is equivalent to the same lower bound for every finite indexed family satisfying the cyclic trace tensor coefficient identities. The third tensor factor is the transpose of the triad output weight.
-/

open Matrix

theorem matrix3_tensor_rank_ge_iff_trace_tensor_bound {R : Type*} [CommSemiring R]
    (r : ℕ) :
    matrix3_tensor_rank_ge R r ↔
    ∀ (n : ℕ) (a b c : Fin n → Matrix (Fin 3) (Fin 3) R),
      (∀ i j j' k k' i' : Fin 3,
        ∑ s, a s i j * b s j' k * c s k' i' =
          if j = j' ∧ k = k' ∧ i = i' then 1 else 0) → r ≤ n := by
  constructor
  · intro h n a b c hc
    have hv := (matrix3_valid_iff_trace_tensor_identity n a b c).mpr hc
    simpa only [List.length_ofFn] using h _ hv
  · intro h L hL
    have hget : (List.ofFn fun s : Fin L.length =>
        (⟨(L.get s).u, (L.get s).v, ((L.get s).wᵀ)ᵀ⟩ : Matrix3Triad R)) = L := by
      simp only [Matrix.transpose_transpose]
      exact List.ofFn_get L
    have hv := hget.symm ▸ hL
    exact h L.length (fun s => (L.get s).u) (fun s => (L.get s).v)
      (fun s => (L.get s).wᵀ)
      ((matrix3_valid_iff_trace_tensor_identity L.length _ _ _).mp hv)
