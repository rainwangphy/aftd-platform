import AFTD.Prelude

/-!
# matrix3_trace_split_reconstruction

Topic: algebraic_complexity   Node: 7872d700376b

Provenance: helper lemma. Helper for OP-1 and matrix3_trace_rank_sum_ge_27 / matrix3_trace_saturation; arXiv:2610.11823v3, Sections 4.1-4.2. The coefficient identity is proved here directly, with no imported lower bound.

The cyclic trace coefficient identities reconstruct every 27-coordinate vector through the first-factor column ranges. This is the explicit right-inverse identity behind the split flattening.
-/

open Matrix Finset

theorem matrix3_trace_split_reconstruction {K : Type*} [Field K] {r : ℕ} (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
    (z : Fin 3 × Fin 3 × Fin 3 → K) (p : Fin 3 × Fin 3 × Fin 3) :
    (∑ s, ((a s) *ᵥ (fun j => ∑ k, ∑ i, c s k i * z (i,j,k))) p.1 *
      b s p.2.1 p.2.2) = z p := by
  rcases p with ⟨i,j,k⟩
  change (∑ s, (∑ j', a s i j' * (∑ k', ∑ i', c s k' i' * z (i',j',k'))) * b s j k) = _
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j'
    rw [Finset.sum_comm]
    arg 2
    ext k'
    rw [Finset.sum_comm]
  simp_rw [show ∀ s j' k' i',
      a s i j' * (c s k' i' * z (i',j',k')) * b s j k =
      (a s i j' * b s j k * c s k' i') * z (i',j',k') by intros; ring,
    ← Finset.sum_mul, h]
  simp [ite_and]
