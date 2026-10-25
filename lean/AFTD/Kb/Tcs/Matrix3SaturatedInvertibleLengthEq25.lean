import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TraceSaturation

/-!
# matrix3_saturated_invertible_length_eq_25

Topic: algebraic_complexity   Node: cb1995fb91a7

Provenance: formalization of a published result. Source: arXiv:2610.11823v3, Lemma 4.3. This formalization works over every field, with the paper's nonzero-factor assumption made explicit; the paper states the two-element-field case.

For a cyclic trace decomposition over a field with every first factor nonzero and the sum of their matrix ranks equal to 27, the existence of an invertible first factor forces the decomposition length to be 25.
-/

open Matrix Finset
noncomputable section
variable {K : Type*} [Field K] {r : ℕ}

private theorem matrix3_saturated_factor_rank_pos {A : Matrix (Fin 3) (Fin 3) K} (hA : A ≠ 0) :
    0 < A.rank := by
  by_contra hn
  have hz : A.rank = 0 := by omega
  have hr : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hz
  have hf : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  apply hA
  ext i j
  have he := congrArg (fun f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) => f (Pi.single j 1) i) hf
  simpa using he
end

theorem matrix3_saturated_invertible_length_eq_25 {K : Type*} [Field K] {r : ℕ} (a b c : Fin r → Matrix (Fin 3) (Fin 3) K)
    (hn : ∀ s, a s ≠ 0)
    (hc : ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0)
    (hd : ∑ s, (a s).rank = 27)
    (t : Fin r) (ht : (a t).det ≠ 0) : r = 25 := by
  have h := matrix3_trace_saturation a b c hc hd
  have hdiag (s : Fin r) : a s * b s * c s * a s = a s := by simpa using h s s
  have hct : (c t).det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det (hdiag t)
    simp only [Matrix.det_mul, hz, mul_zero, zero_mul] at he
    exact ht he.symm
  have hsmall (s : Fin r) (hst : s ≠ t) : (a s).rank = 1 := by
    have hoff : a t * b s * c t * a s = 0 := by simpa [Ne.symm hst] using h t s
    have hz : (b s * c t) * a s = 0 := by
      have he := congrArg (fun M => (a t)⁻¹ * M) hoff
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht),
        Matrix.one_mul, Matrix.mul_zero] using he
    have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
    rw [Matrix.rank_mul_eq_left_of_det_ne_zero (c t) (b s) hct, Fintype.card_fin] at hsum
    have hle : (a s).rank ≤ (b s).rank := by
      calc
        (a s).rank = (a s * b s * c s * a s).rank := congrArg Matrix.rank (hdiag s).symm
        _ ≤ (a s * b s * c s).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (a s * b s).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (b s).rank := Matrix.rank_mul_le_right _ _
    have hp := matrix3_saturated_factor_rank_pos (hn s)
    omega
  have ht3 : (a t).rank = 3 := by simpa using Matrix.rank_of_det_ne_zero ht
  have he : (∑ s, (a s).rank) = ∑ s : Fin r, (1 + if s = t then 2 else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hst : s = t
    · subst s; simp [ht3]
    · simp [hst, hsmall s hst]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at he
  omega
