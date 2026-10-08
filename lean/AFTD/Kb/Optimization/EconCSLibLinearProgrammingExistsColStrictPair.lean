import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingLpWeakDuality
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugFeasibleIff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasLemma
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugRow
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualFeasible
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugA
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugB

/-!
# EconCSLib.LinearProgramming.exists_col_strict_pair

Topic: lp_duality   Node: f8b74028ed9c

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.exists_col_strict_pair`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Per-column strict-CS witness**: for each column `j₀`, there exists an optimal primal-dual pair with `x_{j₀} + (c - uᵀA)_{j₀} > 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators EconCSLib.LinearAlgebra in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **Per-column strict-CS witness**: for each column `j₀`, there exists an optimal primal-dual pair with `x_{j₀} + (c - uᵀA)_{j₀} > 0`. -/
theorem EconCSLib.LinearProgramming.exists_col_strict_pair
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (v : 𝕜)
    {x₀ : Fin n → 𝕜}
    (hx₀A : ∀ i, b i ≤ ∑ j, A i j * x₀ j)
    (hx₀nn : ∀ j, 0 ≤ x₀ j) (hx₀_val : ∑ j, c j * x₀ j = v)
    {u₀ : I → 𝕜} (hu₀ : DualFeasible A c u₀) (hu₀_val : ∑ i, u₀ i * b i = v)
    (j₀ : Fin n) :
    ∃ (x : Fin n → 𝕜) (u : I → 𝕜),
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
      DualFeasible A c u ∧
      (∑ j, c j * x j = v) ∧ (∑ i, u i * b i = v) ∧
      0 < x j₀ + (c j₀ - ∑ i, u i * A i j₀) := by
  classical
  by_cases hCaseA : ∃ x : Fin n → 𝕜,
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
        (∑ j, c j * x j = v) ∧ (0 < x j₀)
  · obtain ⟨x, hxA, hxnn, hcx, hstrict⟩ := hCaseA
    refine ⟨x, u₀, hxA, hxnn, hu₀, hcx, hu₀_val, ?_⟩
    have hu₀_slack : 0 ≤ c j₀ - ∑ i, u₀ i * A i j₀ := by linarith [hu₀.2 j₀]
    linarith
  · push_neg at hCaseA
    have hCaseA' : ∀ x : Fin n → 𝕜,
        (∀ idx, optAugB b v idx ≤ ∑ j, optAugA A c idx j * x j) →
          (0 : 𝕜) ≤ ∑ j, (if j = j₀ then (-1 : 𝕜) else 0) * x j := by
      intro x hx
      obtain ⟨hxA, hxnn, hcx_le⟩ := (optAug_feasible_iff A b c v x).mp hx
      have hcx_ge : v ≤ ∑ j, c j * x j := by
        have hwd := lp_weak_duality A b c hxA hxnn hu₀
        linarith [hu₀_val]
      have hcx_eq : ∑ j, c j * x j = v := le_antisymm hcx_le hcx_ge
      have hxj₀_le : x j₀ ≤ 0 := hCaseA x hxA hxnn hcx_eq
      have hsel : (∑ j, (if j = j₀ then (-1 : 𝕜) else 0) * x j) = -x j₀ := by
        simp [Fintype.sum_ite_eq, ite_mul, neg_mul, one_mul, zero_mul]
      linarith [hsel]
    have hAug_feas : EconCSLib.LinearAlgebra.IsFeasible (optAugA A c) (optAugB b v) :=
      ⟨x₀, (optAug_feasible_iff A b c v x₀).mpr ⟨hx₀A, hx₀nn, hx₀_val.le⟩⟩
    have hCert :=
      (EconCSLib.LinearAlgebra.farkas_lemma (optAugA A c) (optAugB b v)
        (fun j => if j = j₀ then (-1 : 𝕜) else 0) 0 hAug_feas).mp hCaseA'
    obtain ⟨w, hw_nn, hw_col, hw_b⟩ := hCert
    set μ : I → 𝕜 := fun i => w (Sum.inl (Sum.inl i)) with hμ_def
    set ν : Fin n → 𝕜 := fun j' => w (Sum.inl (Sum.inr j')) with hν_def
    set lam : 𝕜 := w (Sum.inr ()) with hlam_def
    have hμ_nn : ∀ i, 0 ≤ μ i := fun i => hw_nn (Sum.inl (Sum.inl i))
    have hν_nn : ∀ j', 0 ≤ ν j' := fun j' => hw_nn (Sum.inl (Sum.inr j'))
    have hlam_nn : 0 ≤ lam := hw_nn (Sum.inr ())
    have sum_split : ∀ (f : OptAugRow I n → 𝕜),
        (∑ idx, f idx) = (∑ i, f (Sum.inl (Sum.inl i)))
          + (∑ j', f (Sum.inl (Sum.inr j'))) + f (Sum.inr ()) := by
      intro f
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have hunit : (∑ u : Unit, f (Sum.inr u)) = f (Sum.inr ()) := by
        rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
      rw [hunit]
    have hcol : ∀ j, (∑ i, μ i * A i j) + ν j - lam * c j = (if j = j₀ then (-1 : 𝕜) else 0) := by
      intro j
      have h := hw_col j
      rw [sum_split] at h
      simp only [optAugA_inl_inl, optAugA_inl_inr, optAugA_inr, mul_ite, mul_one,
                 mul_zero, Fintype.sum_ite_eq] at h
      linarith [h]
    have hb : (∑ i, μ i * b i) - lam * v ≥ 0 := by
      have h := hw_b
      rw [sum_split] at h
      simp only [optAugB_inl_inl, optAugB_inl_inr, mul_zero, Finset.sum_const_zero,
                 optAugB_inr] at h
      linarith [h]
    by_cases hlam_pos : 0 < lam
    · -- Sub-case B.1: lam > 0. Set u = μ / lam.
      refine ⟨x₀, fun i => μ i / lam, hx₀A, hx₀nn, ?_, hx₀_val, ?_, ?_⟩
      · -- DualFeasible
        refine ⟨fun i => div_nonneg (hμ_nn i) hlam_pos.le, ?_⟩
        intro j
        have hkey : (∑ i, μ i * A i j) ≤ lam * c j := by
          have hcol_j := hcol j
          by_cases hjj : j = j₀
          · subst hjj
            simp at hcol_j
            linarith [hν_nn j]
          · simp [hjj] at hcol_j
            linarith [hν_nn j]
        rw [show (∑ i, μ i / lam * A i j) = (∑ i, μ i * A i j) / lam from by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring]
        rw [div_le_iff₀ hlam_pos]; linarith
      · -- ⟨u, b⟩ = v.
        have hub_ge_v : v ≤ ∑ i, μ i / lam * b i := by
          have hkey : (∑ i, μ i * b i) ≥ lam * v := by linarith
          rw [show (∑ i, μ i / lam * b i) = (∑ i, μ i * b i) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [le_div_iff₀ hlam_pos]; linarith
        have hu'_du : DualFeasible A c (fun i => μ i / lam) := by
          refine ⟨fun i => div_nonneg (hμ_nn i) hlam_pos.le, ?_⟩
          intro j
          have hkey : (∑ i, μ i * A i j) ≤ lam * c j := by
            have hcol_j := hcol j
            by_cases hjj : j = j₀
            · subst hjj
              simp at hcol_j
              linarith [hν_nn j]
            · simp [hjj] at hcol_j
              linarith [hν_nn j]
          rw [show (∑ i, μ i / lam * A i j) = (∑ i, μ i * A i j) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [div_le_iff₀ hlam_pos]; linarith
        have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
        linarith [hx₀_val]
      · -- (c - u'ᵀA)_{j₀} > 0 + x₀_{j₀} ≥ 0.
        show 0 < x₀ j₀ + (c j₀ - ∑ i, μ i / lam * A i j₀)
        have hcol_j₀ : (∑ i, μ i * A i j₀) = lam * c j₀ - ν j₀ - 1 := by
          have h := hcol j₀
          simp at h
          linarith
        have hsum_div : (∑ i, μ i / lam * A i j₀) = (∑ i, μ i * A i j₀) / lam := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        rw [hsum_div, hcol_j₀]
        have hx₀_j₀_nn : 0 ≤ x₀ j₀ := hx₀nn j₀
        have hν_nn_j₀ : 0 ≤ ν j₀ := hν_nn j₀
        have hslack_pos : 0 < c j₀ - (lam * c j₀ - ν j₀ - 1) / lam := by
          have heq : c j₀ - (lam * c j₀ - ν j₀ - 1) / lam = (ν j₀ + 1) / lam := by
            field_simp; ring
          rw [heq]
          exact div_pos (by linarith) hlam_pos
        linarith
    · -- Sub-case B.2: lam = 0.
      push_neg at hlam_pos
      have hlam_zero : lam = 0 := le_antisymm hlam_pos hlam_nn
      refine ⟨x₀, fun i => u₀ i + μ i, hx₀A, hx₀nn, ?_, hx₀_val, ?_, ?_⟩
      · -- DualFeasible
        refine ⟨fun i => by linarith [hu₀.1 i, hμ_nn i], ?_⟩
        intro j
        have hcol_j := hcol j
        rw [hlam_zero] at hcol_j
        have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
        by_cases hjj : j = j₀
        · rw [hjj] at hcol_j
          simp at hcol_j
          have hμA_neg : (∑ i, μ i * A i j₀) ≤ -1 := by linarith [hν_nn j₀]
          have hsplit : (∑ i, (u₀ i + μ i) * A i j₀)
              = (∑ i, u₀ i * A i j₀) + (∑ i, μ i * A i j₀) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring
          rw [hjj, hsplit]; linarith [hu₀.2 j₀]
        · simp [hjj] at hcol_j
          have hμA_nn : (∑ i, μ i * A i j) ≤ 0 := by linarith [hν_nn j]
          have hsplit : (∑ i, (u₀ i + μ i) * A i j)
              = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring
          rw [hsplit]; linarith
      · -- ⟨u', b⟩ = v.
        have hub_split : (∑ i, (u₀ i + μ i) * b i)
            = (∑ i, u₀ i * b i) + (∑ i, μ i * b i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        have hμb_nn : (∑ i, μ i * b i) ≥ 0 := by rw [hlam_zero] at hb; linarith
        have hu'_du : DualFeasible A c (fun i => u₀ i + μ i) := by
          refine ⟨fun i => by linarith [hu₀.1 i, hμ_nn i], ?_⟩
          intro j
          have hcol_j := hcol j
          rw [hlam_zero] at hcol_j
          have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
          by_cases hjj : j = j₀
          · rw [hjj] at hcol_j
            simp at hcol_j
            have hμA_neg : (∑ i, μ i * A i j₀) ≤ -1 := by linarith [hν_nn j₀]
            have hsplit : (∑ i, (u₀ i + μ i) * A i j₀)
                = (∑ i, u₀ i * A i j₀) + (∑ i, μ i * A i j₀) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            rw [hjj, hsplit]; linarith [hu₀.2 j₀]
          · simp [hjj] at hcol_j
            have hμA_nn : (∑ i, μ i * A i j) ≤ 0 := by linarith [hν_nn j]
            have hsplit : (∑ i, (u₀ i + μ i) * A i j)
                = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            rw [hsplit]; linarith
        have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
        rw [hub_split]
        linarith [hx₀_val, hu₀_val]
      · -- (c - u'ᵀA)_{j₀} > 0.
        show 0 < x₀ j₀ + (c j₀ - ∑ i, (u₀ i + μ i) * A i j₀)
        have hcol_j₀ : (∑ i, μ i * A i j₀) = -1 - ν j₀ := by
          have h := hcol j₀
          simp at h
          rw [hlam_zero] at h; linarith
        have hsplit : (∑ i, (u₀ i + μ i) * A i j₀)
            = (∑ i, u₀ i * A i j₀) + (∑ i, μ i * A i j₀) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        rw [hsplit, hcol_j₀]
        have h_u₀A : (∑ i, u₀ i * A i j₀) ≤ c j₀ := hu₀.2 j₀
        have hx₀_j₀_nn : 0 ≤ x₀ j₀ := hx₀nn j₀
        have hν_nn_j₀ : 0 ≤ ν j₀ := hν_nn j₀
        linarith
