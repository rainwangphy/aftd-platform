import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualFeasible
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugRow
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugB
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugA
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugFeasibleIff
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingLpWeakDuality
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasLemma
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef
import AFTD.Kb.GameTheoryEconomics.Strict

/-!
# EconCSLib.LinearProgramming.exists_row_strict_pair

Topic: lp_duality   Node: 48b2b2f0dd5e

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.exists_row_strict_pair`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Per-row strict-CS witness**: for each row `i₀`, there exists an optimal primal-dual pair with `(Ax - b)_{i₀} + u_{i₀} > 0`. Hypotheses: * `hx₀` — `x₀` is primal-feasible with `⟨c, x₀⟩ = v` (primal-optimal). * `hu₀` — `u₀` is dual-feasible with `⟨u₀, b⟩ = v` (dual-optimal). Both `x₀` and `u₀` exist by LP strong duality when both P and D are feasible.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators EconCSLib.LinearAlgebra in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **Per-row strict-CS witness**: for each row `i₀`, there exists an optimal primal-dual pair with `(Ax - b)_{i₀} + u_{i₀} > 0`. Hypotheses: * `hx₀` — `x₀` is primal-feasible with `⟨c, x₀⟩ = v` (primal-optimal). * `hu₀` — `u₀` is dual-feasible with `⟨u₀, b⟩ = v` (dual-optimal). Both `x₀` and `u₀` exist by LP strong duality when both P and D are feasible. -/
theorem EconCSLib.LinearProgramming.exists_row_strict_pair
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (v : 𝕜)
    {x₀ : Fin n → 𝕜}
    (hx₀A : ∀ i, b i ≤ ∑ j, A i j * x₀ j)
    (hx₀nn : ∀ j, 0 ≤ x₀ j) (hx₀_val : ∑ j, c j * x₀ j = v)
    {u₀ : I → 𝕜} (hu₀ : DualFeasible A c u₀) (hu₀_val : ∑ i, u₀ i * b i = v)
    (i₀ : I) :
    ∃ (x : Fin n → 𝕜) (u : I → 𝕜),
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
      DualFeasible A c u ∧
      (∑ j, c j * x j = v) ∧ (∑ i, u i * b i = v) ∧
      0 < (∑ j, A i₀ j * x j - b i₀) + u i₀ := by
  classical
  -- Classical case split.
  by_cases hCaseA : ∃ x : Fin n → 𝕜,
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
        (∑ j, c j * x j = v) ∧ (b i₀ < ∑ j, A i₀ j * x j)
  · -- Case A: primal-optimal x with strict row slack at i₀.
    obtain ⟨x, hxA, hxnn, hcx, hstrict⟩ := hCaseA
    refine ⟨x, u₀, hxA, hxnn, hu₀, hcx, hu₀_val, ?_⟩
    have hu₀nn : 0 ≤ u₀ i₀ := hu₀.1 i₀
    linarith
  · -- Case B: ∀ primal-optimal x, (Ax - b)_{i₀} ≤ 0 (forced = 0 by Ax ≥ b).
    -- We now construct a dual-optimal u with u_{i₀} > 0 via Farkas.
    push_neg at hCaseA
    -- hCaseA : ∀ x, (Ax ≥ b) → (x ≥ 0) → (⟨c,x⟩ = v) → (Ax)_{i₀} ≤ b_{i₀}
    -- Encode "primal-optimal" as "primal-feasible + ⟨c, x⟩ ≤ v"; combined
    -- with weak duality (⟨c, x⟩ ≥ v), this is "= v".
    have hCaseA' : ∀ x : Fin n → 𝕜,
        (∀ idx, optAugB b v idx ≤ ∑ j, optAugA A c idx j * x j) →
          -b i₀ ≤ ∑ j, (-A i₀ j) * x j := by
      intro x hx
      obtain ⟨hxA, hxnn, hcx_le⟩ := (optAug_feasible_iff A b c v x).mp hx
      -- Weak duality forces ⟨c, x⟩ ≥ ⟨u₀, b⟩ = v.
      have hcx_ge : v ≤ ∑ j, c j * x j := by
        have hwd := lp_weak_duality A b c hxA hxnn hu₀
        linarith [hu₀_val]
      have hcx_eq : ∑ j, c j * x j = v := le_antisymm hcx_le hcx_ge
      have hAi₀ := hCaseA x hxA hxnn hcx_eq
      have hsum_neg : (∑ j, -A i₀ j * x j) = -(∑ j, A i₀ j * x j) := by
        simp [Finset.sum_neg_distrib, neg_mul]
      linarith [hsum_neg]
    -- Apply Farkas. First, feasibility of the augmented system:
    have hAug_feas : EconCSLib.LinearAlgebra.IsFeasible (optAugA A c) (optAugB b v) :=
      ⟨x₀, (optAug_feasible_iff A b c v x₀).mpr ⟨hx₀A, hx₀nn, hx₀_val.le⟩⟩
    -- Farkas yields the certificate.
    have hCert :=
      (EconCSLib.LinearAlgebra.farkas_lemma (optAugA A c) (optAugB b v)
        (fun j => -A i₀ j) (-b i₀) hAug_feas).mp hCaseA'
    obtain ⟨w, hw_nn, hw_col, hw_b⟩ := hCert
    -- Decompose w into (μ, ν, λ) over (I, Fin n, Unit).
    set μ : I → 𝕜 := fun i => w (Sum.inl (Sum.inl i)) with hμ_def
    set ν : Fin n → 𝕜 := fun j' => w (Sum.inl (Sum.inr j')) with hν_def
    set lam : 𝕜 := w (Sum.inr ()) with hlam_def
    have hμ_nn : ∀ i, 0 ≤ μ i := fun i => hw_nn (Sum.inl (Sum.inl i))
    have hν_nn : ∀ j', 0 ≤ ν j' := fun j' => hw_nn (Sum.inl (Sum.inr j'))
    have hlam_nn : 0 ≤ lam := hw_nn (Sum.inr ())
    -- Helper: reduce the OptAugRow sum to its three components.
    have sum_split : ∀ (f : OptAugRow I n → 𝕜),
        (∑ idx, f idx) = (∑ i, f (Sum.inl (Sum.inl i)))
          + (∑ j', f (Sum.inl (Sum.inr j'))) + f (Sum.inr ()) := by
      intro f
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have hunit : (∑ u : Unit, f (Sum.inr u)) = f (Sum.inr ()) := by
        rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
      rw [hunit]
    -- Translate the column condition into `(μ + e_{i₀})ᵀ A + ν - lam c = -A i₀`.
    have hcol : ∀ j, (∑ i, μ i * A i j) + ν j - lam * c j = -A i₀ j := by
      intro j
      have h := hw_col j
      rw [sum_split] at h
      simp only [optAugA_inl_inl, optAugA_inl_inr, optAugA_inr, mul_ite, mul_one,
                 mul_zero, Fintype.sum_ite_eq] at h
      linarith [h]
    -- Translate the RHS condition: ⟨μ, b⟩ - lam * v ≥ -b_{i₀}.
    have hb : (∑ i, μ i * b i) - lam * v ≥ -b i₀ := by
      have h := hw_b
      rw [sum_split] at h
      simp only [optAugB_inl_inl, optAugB_inl_inr, mul_zero, Finset.sum_const_zero,
                 optAugB_inr] at h
      linarith [h]
    -- Now case-split on lam.
    by_cases hlam_pos : 0 < lam
    · -- Sub-case B.1: lam > 0. Set u = (μ + e_{i₀}) / lam.
      refine ⟨x₀, fun i => (μ i + (if i = i₀ then 1 else 0)) / lam, hx₀A, hx₀nn, ?_, hx₀_val,
              ?_, ?_⟩
      · -- DualFeasible
        refine ⟨?_, ?_⟩
        · intro i
          have hsum_nn : 0 ≤ μ i + (if i = i₀ then 1 else 0) := by
            have : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by
              split_ifs <;> simp
            linarith [hμ_nn i]
          exact div_nonneg hsum_nn hlam_pos.le
        · intro j
          -- (∑ i, (μ_i + e_{i₀,i}) / lam * A i j) ≤ c j.
          have hkey : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) ≤ lam * c j := by
            -- From hcol: ∑ i μ_i A_ij + ν_j - lam c_j = -A_{i₀,j}
            -- Rearrange: ∑ i (μ_i + e_{i₀,i}) A_ij = lam c_j - ν_j ≤ lam c_j
            have hsplit : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                = (∑ i, μ i * A i j) + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
              simp [Fintype.sum_ite_eq]
            have hsplit2 : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                = (∑ i, μ i * A i j) + A i₀ j := by rw [hsplit, hsel]
            have hreorg : (∑ i, μ i * A i j) + A i₀ j = lam * c j - ν j := by linarith [hcol j]
            rw [hsplit2, hreorg]
            linarith [hν_nn j]
          rw [show (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * A i j)
              = (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [div_le_iff₀ hlam_pos]; linarith
      · -- ⟨u, b⟩ = v: equals from ≥ v (Farkas) and ≤ v (weak duality).
        have hub_ge_v : v ≤ ∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * b i := by
          -- (⟨μ, b⟩ + b_{i₀}) / lam ≥ v from hb (since ⟨μ, b⟩ - lam v ≥ -b_{i₀}).
          have hkey : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * b i) ≥ lam * v := by
            have hsplit : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * b i)
                = (∑ i, μ i * b i) + (∑ i, (if i = i₀ then 1 else 0) * b i) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * b i) = b i₀ := by
              simp [Fintype.sum_ite_eq]
            rw [hsplit, hsel]; linarith [hb]
          rw [show (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * b i)
              = (∑ i, (μ i + (if i = i₀ then 1 else 0)) * b i) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [le_div_iff₀ hlam_pos]; linarith
        have hub_le_v : (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * b i) ≤ v := by
          have hu'_du : DualFeasible A c (fun i => (μ i + (if i = i₀ then 1 else 0)) / lam) := by
            refine ⟨?_, ?_⟩
            · intro i
              have hsum_nn : 0 ≤ μ i + (if i = i₀ then 1 else 0) := by
                have : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by
                  split_ifs <;> simp
                linarith [hμ_nn i]
              exact div_nonneg hsum_nn hlam_pos.le
            · intro j
              have hkey : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) ≤ lam * c j := by
                have hsplit : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                    = (∑ i, μ i * A i j) + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl (fun i _ => ?_); ring
                have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
                  simp [Fintype.sum_ite_eq]
                have hsplit2 : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                    = (∑ i, μ i * A i j) + A i₀ j := by rw [hsplit, hsel]
                have hreorg : (∑ i, μ i * A i j) + A i₀ j = lam * c j - ν j := by linarith [hcol j]
                rw [hsplit2, hreorg]
                linarith [hν_nn j]
              rw [show (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * A i j)
                  = (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) / lam from by
                rw [Finset.sum_div]
                refine Finset.sum_congr rfl (fun i _ => ?_); ring]
              rw [div_le_iff₀ hlam_pos]; linarith
          have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
          linarith [hx₀_val]
        linarith
      · -- (Ax₀ - b)_{i₀} + u_{i₀} > 0.
        show 0 < (∑ j, A i₀ j * x₀ j - b i₀) + (μ i₀ + (if i₀ = i₀ then 1 else 0)) / lam
        have hu_i₀_pos : 0 < (μ i₀ + (if i₀ = i₀ then 1 else 0)) / lam := by
          have : μ i₀ + (if i₀ = i₀ then (1 : 𝕜) else 0) ≥ 1 := by
            simp; linarith [hμ_nn i₀]
          exact div_pos (by linarith) hlam_pos
        have hAx_nn : 0 ≤ ∑ j, A i₀ j * x₀ j - b i₀ := by linarith [hx₀A i₀]
        linarith
    · -- Sub-case B.2: lam ≤ 0 (i.e., lam = 0 since lam ≥ 0).
      push_neg at hlam_pos
      have hlam_zero : lam = 0 := le_antisymm hlam_pos hlam_nn
      -- u' = u₀ + (μ + e_{i₀}).
      refine ⟨x₀, fun i => u₀ i + μ i + (if i = i₀ then 1 else 0), hx₀A, hx₀nn, ?_, hx₀_val,
              ?_, ?_⟩
      · -- DualFeasible
        refine ⟨?_, ?_⟩
        · intro i
          have h1 : 0 ≤ u₀ i := hu₀.1 i
          have h2 : 0 ≤ μ i := hμ_nn i
          have h3 : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by split_ifs <;> simp
          linarith
        · intro j
          -- ((u₀)ᵀA)_j + ((μ + e_{i₀})ᵀA)_j ≤ c_j + 0 = c_j (since lam = 0).
          have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
          have hcol_j := hcol j
          rw [hlam_zero] at hcol_j
          -- hcol_j : (∑ i, μ i * A i j) + ν j - 0 = -A i₀ j
          --        i.e., (∑ i, μ i * A i j) = -A i₀ j - ν j ≤ -A i₀ j
          have h_μA_le : (∑ i, μ i * A i j) + A i₀ j ≤ 0 := by linarith [hν_nn j]
          have hsplit : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * A i j)
              = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j)
                + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring
          have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
            simp [Fintype.sum_ite_eq]
          rw [hsplit, hsel]
          linarith
      · -- ⟨u', b⟩ = v.
        have hub_split : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * b i)
            = (∑ i, u₀ i * b i) + (∑ i, μ i * b i)
              + (∑ i, (if i = i₀ then 1 else 0) * b i) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * b i) = b i₀ := by
          simp [Fintype.sum_ite_eq]
        rw [hub_split, hsel]
        -- From hb with lam = 0: ⟨μ, b⟩ ≥ -b_{i₀}, i.e., ⟨μ, b⟩ + b_{i₀} ≥ 0.
        have hμb_ge : (∑ i, μ i * b i) + b i₀ ≥ 0 := by
          rw [hlam_zero] at hb; linarith
        -- Apply weak duality on the new u' to get ⟨u', b⟩ ≤ v.
        have hu'_du : DualFeasible A c (fun i => u₀ i + μ i + (if i = i₀ then 1 else 0)) := by
          refine ⟨?_, ?_⟩
          · intro i
            have h1 : 0 ≤ u₀ i := hu₀.1 i
            have h2 : 0 ≤ μ i := hμ_nn i
            have h3 : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by split_ifs <;> simp
            linarith
          · intro j
            have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
            have hcol_j := hcol j
            rw [hlam_zero] at hcol_j
            have h_μA_le : (∑ i, μ i * A i j) + A i₀ j ≤ 0 := by linarith [hν_nn j]
            have hsplit : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * A i j)
                = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j)
                  + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            have hsel2 : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
              simp [Fintype.sum_ite_eq]
            rw [hsplit, hsel2]
            linarith
        have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
        -- hwd : ∑ i, u' i * b i ≤ ∑ j, c j * x₀ j = v
        have hwd' : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * b i) ≤ v := by
          have := hwd
          rw [hx₀_val] at this; exact this
        rw [hub_split, hsel] at hwd'
        linarith [hu₀_val]
      · -- (Ax₀ - b)_{i₀} + u'_{i₀} > 0.
        have hu'_i₀ : (u₀ i₀ + μ i₀ + (if i₀ = i₀ then 1 else 0)) ≥ 1 := by
          have h1 : 0 ≤ u₀ i₀ := hu₀.1 i₀
          have h2 : 0 ≤ μ i₀ := hμ_nn i₀
          simp; linarith
        have hAx_nn : 0 ≤ ∑ j, A i₀ j * x₀ j - b i₀ := by linarith [hx₀A i₀]
        linarith
