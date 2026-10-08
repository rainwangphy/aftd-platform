import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.GameTheoryEconomics.SkewSymmetricRow
import AFTD.Kb.GameTheoryEconomics.SkewSymmetricMat
import AFTD.Kb.GameTheoryEconomics.SkewSymmetricRhs
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraHasCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraTheoremOfAlternative
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef

/-!
# SkewSymmetric.optimal

Topic: equilibria   Node: 0692bc91ce21

Provenance: formalization of a published result. Source: EconCSLib, `SkewSymmetric.optimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/SkewSymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Skew-symmetric optimal strategy.** Every skew-symmetric game has a value-0 optimal mixed strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.LinearAlgebra in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {N : ℕ} in
/-- **Skew-symmetric optimal strategy.** Every skew-symmetric game has a value-0 optimal mixed strategy. -/
theorem SkewSymmetric.optimal [NeZero N] (S : Fin N → Fin N → 𝕜) (hS : ∀ k l, S k l = - S l k) :
    ∃ z : Fin N → 𝕜, (∀ k, 0 ≤ z k) ∧ (∑ k, z k = 1) ∧ (∀ l, 0 ≤ ∑ k, z k * S k l) := by
  classical
  -- Feasibility of the system, via the Theorem of the Alternative.
  have hfeas : IsFeasible (mat S) (rhs (N := N)) := by
    by_contra hno
    obtain ⟨u, hu_nn, hu_col, hu_pos⟩ :=
      (theorem_of_alternative (mat S) (rhs (N := N))).mp hno
    -- Block abbreviations.
    set w : Fin N → 𝕜 := fun l => u (Sum.inl l) with hw
    have hw_nn : ∀ l, 0 ≤ w l := fun l => hu_nn _
    have hv_nn : ∀ k, 0 ≤ u (Sum.inr (Sum.inl k)) := fun k => hu_nn _
    set a0 : 𝕜 := u (Sum.inr (Sum.inr false)) with ha0
    set a1 : 𝕜 := u (Sum.inr (Sum.inr true)) with ha1
    -- ⟨u, b⟩ = a0 - a1 > 0.
    have hδ : 0 < a0 - a1 := by
      have h := hu_pos
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_bool] at h
      simp only [rhs, mul_zero, Finset.sum_const_zero, zero_add, mul_one,
        mul_neg, mul_one] at h
      linarith
    -- Column-`j` condition collapses to `(S w)_j + u(inr inl j) + (a0 - a1) = 0`.
    have hcol : ∀ j, (∑ l, S j l * w l) + u (Sum.inr (Sum.inl j)) + (a0 - a1) = 0 := by
      intro j
      have h := hu_col j
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_bool] at h
      simp only [mat, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, mul_neg, hw] at h
      -- h : (∑ l, u (inl l) * S j l) + (u (inr (inl j)) + (a0 + -a1)) = 0
      have e : (∑ l, u (Sum.inl l) * S j l) = ∑ l, S j l * w l := by
        refine Finset.sum_congr rfl (fun l _ => ?_); rw [hw]; ring
      rw [e] at h; linarith
    -- The certificate vector `w` is the bad alternative `S w < 0`.
    have hSw : ∀ j, (∑ l, S j l * w l) ≤ -(a0 - a1) := by
      intro j; have := hcol j; have := hv_nn j; linarith
    -- `w ≠ 0`: otherwise `(S w)_j = 0`, contradicting `≤ -(a0-a1) < 0`.
    have hw_pos : 0 < ∑ l, w l := by
      rcases (Finset.sum_nonneg (fun l _ => hw_nn l)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hall : ∀ l, w l = 0 := fun l =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hw_nn l)).mp h.symm l (Finset.mem_univ l)
        have hj : (∑ l, S ((0 : Fin N)) l * w l) = 0 := by
          apply Finset.sum_eq_zero; intro l _; rw [hall l, mul_zero]
        have := hSw (0 : Fin N); rw [hj] at this; linarith
    -- Antisymmetry: `wᵀ S w = 0`.
    have hQ0 : (∑ j, ∑ l, w j * S j l * w l) = 0 := by
      have hswap : (∑ j, ∑ l, w j * S j l * w l)
          = ∑ j, ∑ l, w l * S l j * w j := Finset.sum_comm
      have hneg : (∑ j, ∑ l, w l * S l j * w j)
          = - ∑ j, ∑ l, w j * S j l * w l := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hS l j]; ring
      have : (∑ j, ∑ l, w j * S j l * w l)
          = - ∑ j, ∑ l, w j * S j l * w l := hswap.trans hneg
      linarith
    -- But `wᵀ S w = ∑ⱼ wⱼ (Sw)ⱼ ≤ -(a0-a1) · ∑w < 0`.
    have hQeq : (∑ j, w j * (∑ l, S j l * w l)) = ∑ j, ∑ l, w j * S j l * w l := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => ?_); ring
    have hle : (∑ j, w j * (∑ l, S j l * w l)) ≤ ∑ j, w j * (-(a0 - a1)) := by
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left (hSw j) (hw_nn j)
    rw [hQeq, hQ0] at hle
    have hrhs : (∑ j, w j * (-(a0 - a1))) = -(a0 - a1) * ∑ j, w j := by
      rw [← Finset.sum_mul]; ring
    rw [hrhs] at hle
    have : -(a0 - a1) * (∑ j, w j) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hw_pos
    linarith
  -- Extract `z` from a feasible point.
  obtain ⟨z, hz⟩ := hfeas
  refine ⟨z, ?_, ?_, ?_⟩
  · intro k
    have h := hz (Sum.inr (Sum.inl k))
    simp only [rhs, rowEval, mat, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  · have h0 := hz (Sum.inr (Sum.inr false))
    have h1 := hz (Sum.inr (Sum.inr true))
    simp only [rhs, rowEval, mat, one_mul, neg_one_mul, Finset.sum_neg_distrib] at h0 h1
    linarith
  · intro l
    have h := hz (Sum.inl l)
    simp only [rhs, rowEval, mat] at h
    rw [show (∑ k, z k * S k l) = ∑ j, S j l * z j from
      Finset.sum_congr rfl (fun j _ => by ring)]
    exact h
