import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugRow
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugA
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugB
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingPrimalFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugAInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugAInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugBInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef

/-!
# EconCSLib.LinearProgramming.isFeasible_dualAug_iff

Topic: lp_duality   Node: 2c2d4cd4eb6d

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.isFeasible_dualAug_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Augmented feasibility is the primal feasibility (with `x ≥ 0`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators EconCSLib.LinearAlgebra in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Augmented feasibility is the primal feasibility (with `x ≥ 0`). -/
theorem EconCSLib.LinearProgramming.isFeasible_dualAug_iff (A : I → Fin n → 𝕜) (b : I → 𝕜) :
    IsFeasible (dualAugA A) (dualAugB b) ↔ PrimalFeasible A b := by
  unfold IsFeasible PrimalFeasible
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · intro i
      have h := hx (Sum.inl i)
      simpa [rowEval] using h
    · intro j'
      have h := hx (Sum.inr j')
      -- h : 0 ≤ ∑ j, (if j = j' then 1 else 0) * x j = x j'
      simp only [rowEval, dualAugB_inr, dualAugA_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq'] at h
      exact h
  · rintro ⟨x, hxA, hxnn⟩
    refine ⟨x, ?_⟩
    intro idx
    rcases idx with i | j'
    · simp only [rowEval, dualAugB_inl, dualAugA_inl]
      exact hxA i
    · simp only [rowEval, dualAugB_inr, dualAugA_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq']
      exact hxnn j'
