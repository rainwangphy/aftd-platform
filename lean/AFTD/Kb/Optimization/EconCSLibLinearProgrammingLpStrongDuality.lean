import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingPrimalFeasible
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugRow
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugA
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugB
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingIsFeasibleDualAugIff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasLemma
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugAInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugAInr
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugBInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef

/-!
# EconCSLib.LinearProgramming.lp_strong_duality

Topic: lp_duality   Node: 3ea655ca7bb9

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.lp_strong_duality`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**LP Strong Duality** [MFoGT, Section 2.8, Exercise 9]: if the primal LP `min ⟨c, x⟩ s.t. A x ≥ b, x ≥ 0` is feasible and bounded below by `d`, then there exists a dual-feasible `u` with `⟨u, b⟩ ≥ d`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators EconCSLib.LinearAlgebra in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **LP Strong Duality** [MFoGT, Section 2.8, Exercise 9]: if the primal LP `min ⟨c, x⟩ s.t. A x ≥ b, x ≥ 0` is feasible and bounded below by `d`, then there exists a dual-feasible `u` with `⟨u, b⟩ ≥ d`. -/
theorem EconCSLib.LinearProgramming.lp_strong_duality (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (d : 𝕜)
    (hP_feas : PrimalFeasible A b)
    (hP_bound : ∀ x : Fin n → 𝕜,
      (∀ i, b i ≤ ∑ j, A i j * x j) → (∀ j, 0 ≤ x j) → d ≤ ∑ j, c j * x j) :
    ∃ u : I → 𝕜, DualFeasible A c u ∧ d ≤ ∑ i, u i * b i := by
  -- Translate hypotheses to the augmented system.
  have hAug_feas : IsFeasible (dualAugA A) (dualAugB b) :=
    (isFeasible_dualAug_iff A b).mpr hP_feas
  have hAug_bound : ∀ x : Fin n → 𝕜,
      (∀ idx, dualAugB b idx ≤ ∑ j, dualAugA A idx j * x j) →
      d ≤ ∑ j, c j * x j := by
    intro x hx
    apply hP_bound x
    · intro i
      have h := hx (Sum.inl i)
      simpa using h
    · intro j'
      have h := hx (Sum.inr j')
      simp only [dualAugB_inr, dualAugA_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq'] at h
      exact h
  -- Apply Farkas to the augmented system.
  have hCert := (farkas_lemma (dualAugA A) (dualAugB b) c d hAug_feas).mp hAug_bound
  obtain ⟨u_aug, hu_nn, hu_col, hu_b⟩ := hCert
  -- Decompose u_aug into u (on I) and v (on Fin n).
  refine ⟨fun i => u_aug (Sum.inl i), ?_, ?_⟩
  · -- DualFeasible: u ≥ 0 and uᵀA ≤ c.
    refine ⟨fun i => hu_nn (Sum.inl i), ?_⟩
    intro j
    -- Use the column-j condition on the augmented system.
    have h := hu_col j
    -- h : (∑ row, u_aug row * dualAugA A row j) = c j
    rw [Fintype.sum_sum_type] at h
    -- h : (∑ i, u_aug (Sum.inl i) * dualAugA A (Sum.inl i) j) +
    --     (∑ j', u_aug (Sum.inr j') * dualAugA A (Sum.inr j') j) = c j
    simp only [dualAugA_inl, dualAugA_inr, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
               Fintype.sum_ite_eq, Fintype.sum_ite_eq'] at h
    -- h : (∑ i, u_aug (inl i) * A i j) + u_aug (Sum.inr j) = c j
    -- Goal: ∑ i, u_aug (Sum.inl i) * A i j ≤ c j
    have hv_nn : 0 ≤ u_aug (Sum.inr j) := hu_nn (Sum.inr j)
    linarith
  · -- ⟨u, b⟩ ≥ d
    have h : (∑ row, u_aug row * dualAugB b row) = ∑ i, u_aug (Sum.inl i) * b i := by
      rw [Fintype.sum_sum_type]
      simp only [dualAugB_inl, dualAugB_inr, mul_zero, Finset.sum_const_zero, add_zero]
    linarith [hu_b, h.symm ▸ hu_b]
