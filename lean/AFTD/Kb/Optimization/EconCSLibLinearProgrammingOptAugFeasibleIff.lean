import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugRow
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugB
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugA
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInl

/-!
# EconCSLib.LinearProgramming.optAug_feasible_iff

Topic: lp_duality   Node: 6b58526e310c

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.optAug_feasible_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An `x` satisfies `optAugA · x ≥ optAugB` iff `x` is primal-feasible and has objective at most `v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- An `x` satisfies `optAugA · x ≥ optAugB` iff `x` is primal-feasible and has objective at most `v`. -/
theorem EconCSLib.LinearProgramming.optAug_feasible_iff (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜)
    (v : 𝕜) (x : Fin n → 𝕜) :
    (∀ idx, optAugB b v idx ≤ ∑ j, optAugA A c idx j * x j) ↔
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
        (∑ j, c j * x j ≤ v) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have h1 := h (Sum.inl (Sum.inl i))
      simpa using h1
    · intro j'
      have h1 := h (Sum.inl (Sum.inr j'))
      simp only [optAugB_inl_inr, optAugA_inl_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq'] at h1
      exact h1
    · have h1 := h (Sum.inr ())
      simp only [optAugB_inr, optAugA_inr] at h1
      have : (∑ j, -c j * x j) = -(∑ j, c j * x j) := by
        simp [Finset.sum_neg_distrib, neg_mul]
      linarith [this ▸ h1]
  · rintro ⟨hAx, hxnn, hcx⟩ idx
    rcases idx with ⟨i | j'⟩ | ⟨⟩
    · simpa using hAx i
    · simp only [optAugB_inl_inr, optAugA_inl_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq']
      exact hxnn j'
    · show optAugB b v (Sum.inr ()) ≤ ∑ j, optAugA A c (Sum.inr ()) j * x j
      simp only [optAugB_inr, optAugA_inr]
      have : (∑ j, -c j * x j) = -(∑ j, c j * x j) := by
        simp [Finset.sum_neg_distrib, neg_mul]
      linarith [this]
