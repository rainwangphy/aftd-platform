import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxSymMat
import AFTD.Kb.GameTheoryEconomics.MinimaxSkewOptimal
import AFTD.Kb.GameTheoryEconomics.MinimaxSymMatSkew
import AFTD.Kb.GameTheoryEconomics.MinimaxSumBlocks

/-!
# Minimax.minimax_pos

Topic: equilibria   Node: 29d0450dc88b

Provenance: formalization of a published result. Source: EconCSLib, `Minimax.minimax_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Minimax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Minimax for a strictly positive game.**
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J] in
/-- **Minimax for a strictly positive game.** -/
theorem Minimax.minimax_pos (A : I → J → 𝕜) (hA : ∀ i j, 0 < A i j) :
    ∃ (x : I → 𝕜) (y : J → 𝕜) (v : 𝕜),
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ (∀ j, 0 ≤ y j) ∧ (∑ j, y j = 1) ∧
      (∀ j, v ≤ ∑ i, x i * A i j) ∧ (∀ i, ∑ j, A i j * y j ≤ v) := by
  classical
  obtain ⟨z, hz_nn, hz_sum, hz_col⟩ := skew_optimal (symMat A) (symMat_skew A)
  set p : I → 𝕜 := fun i => z (Sum.inl i) with hp
  set q : J → 𝕜 := fun j => z (Sum.inr (Sum.inl j)) with hq
  set lam : 𝕜 := z (Sum.inr (Sum.inr ())) with hlam
  have hpe : ∀ i, z (Sum.inl i) = p i := fun _ => rfl
  have hqe : ∀ j, z (Sum.inr (Sum.inl j)) = q j := fun _ => rfl
  have hle : z (Sum.inr (Sum.inr ())) = lam := rfl
  have hp_nn : ∀ i, 0 ≤ p i := fun i => hz_nn _
  have hq_nn : ∀ j, 0 ≤ q j := fun j => hz_nn _
  have hlam_nn : 0 ≤ lam := hz_nn _
  -- Column `inl i`: `(A q)_i ≤ λ`.
  have hcolI : ∀ i, (∑ j, A i j * q j) ≤ lam := by
    intro i
    have h := hz_col (Sum.inl i)
    rw [sum_blocks] at h
    simp only [symMat, hpe, hqe, hle, mul_zero, Finset.sum_const_zero, zero_add,
      mul_one] at h
    have hb : (∑ j, q j * -(A i j)) = -(∑ j, A i j * q j) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hb] at h; linarith
  -- Column `inr (inl j)`: `λ ≤ (p A)_j`.
  have hcolJ : ∀ j, lam ≤ ∑ i, p i * A i j := by
    intro j
    have h := hz_col (Sum.inr (Sum.inl j))
    rw [sum_blocks] at h
    simp only [symMat, hpe, hqe, hle, mul_zero, Finset.sum_const_zero, add_zero,
      mul_neg_one] at h
    linarith
  -- Column `inr (inr ())`: `∑ p ≤ ∑ q`.
  have hcolU : (∑ i, p i) ≤ ∑ j, q j := by
    have h := hz_col (Sum.inr (Sum.inr ()))
    rw [sum_blocks] at h
    simp only [symMat, hpe, hqe, hle, mul_one, mul_neg_one, mul_zero, add_zero] at h
    rw [Finset.sum_neg_distrib] at h; linarith
  -- `∑ p > 0`.
  have hsump_pos : 0 < ∑ i, p i := by
    rcases (Finset.sum_nonneg (fun i _ => hp_nn i)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hp0 : ∀ i, p i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp_nn i)).mp heq.symm i (Finset.mem_univ i)
      obtain ⟨j₀⟩ := ‹Nonempty J›
      have hlam0 : lam ≤ 0 := by
        have hz := hcolJ j₀
        rw [show (∑ i, p i * A i j₀) = 0 from
          Finset.sum_eq_zero (fun i _ => by rw [hp0 i, zero_mul])] at hz
        exact hz
      have hlam_eq0 : lam = 0 := le_antisymm hlam0 hlam_nn
      have hsumq1 : (∑ j, q j) = 1 := by
        have hs := hz_sum
        rw [sum_blocks z] at hs
        simp only [hpe, hqe, hle] at hs
        rw [show (∑ i, p i) = 0 from heq.symm, hlam_eq0] at hs; linarith
      obtain ⟨i₀⟩ := ‹Nonempty I›
      have hAq_pos : 0 < ∑ j, A i₀ j * q j := by
        obtain ⟨j₁, -, hj₁⟩ : ∃ j ∈ (Finset.univ : Finset J), 0 < q j := by
          by_contra hc; push_neg at hc
          exact one_ne_zero (hsumq1.symm.trans
            (Finset.sum_eq_zero (fun j hj => le_antisymm (hc j hj) (hq_nn j))))
        exact Finset.sum_pos' (fun j _ => mul_nonneg (hA i₀ j).le (hq_nn j))
          ⟨j₁, Finset.mem_univ j₁, mul_pos (hA i₀ j₁) hj₁⟩
      have := hcolI i₀; linarith
  -- `∑ q > 0`.
  have hsumq_pos : 0 < ∑ j, q j := lt_of_lt_of_le hsump_pos hcolU
  -- Normalise: `x = p / ∑p`, `y = q / ∑q`, value `λ / ∑p`.
  refine ⟨fun i => p i / (∑ i, p i), fun j => q j / (∑ j, q j), lam / (∑ i, p i),
    fun i => div_nonneg (hp_nn i) hsump_pos.le, ?_,
    fun j => div_nonneg (hq_nn j) hsumq_pos.le, ?_, ?_, ?_⟩
  · simp only [div_eq_mul_inv]; rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hsump_pos.ne'
  · simp only [div_eq_mul_inv]; rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hsumq_pos.ne'
  · intro j
    have hkey : (∑ i, p i / (∑ i, p i) * A i j) = (∑ i, p i * A i j) / (∑ i, p i) := by
      simp only [div_eq_mul_inv]; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hkey]
    exact (div_le_div_iff₀ hsump_pos hsump_pos).mpr
      (mul_le_mul_of_nonneg_right (hcolJ j) hsump_pos.le)
  · intro i
    have hkey : (∑ j, A i j * (q j / (∑ j, q j))) = (∑ j, A i j * q j) / (∑ j, q j) := by
      simp only [div_eq_mul_inv]; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hkey]
    refine (div_le_div_iff₀ hsumq_pos hsump_pos).mpr ?_
    calc (∑ j, A i j * q j) * (∑ i, p i)
        ≤ lam * (∑ i, p i) := mul_le_mul_of_nonneg_right (hcolI i) hsump_pos.le
      _ ≤ lam * (∑ j, q j) := mul_le_mul_of_nonneg_left hcolU hlam_nn
