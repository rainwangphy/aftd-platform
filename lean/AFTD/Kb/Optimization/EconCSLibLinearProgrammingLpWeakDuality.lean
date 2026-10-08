import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualFeasible

/-!
# EconCSLib.LinearProgramming.lp_weak_duality

Topic: lp_duality   Node: 57b487eb00d8

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.lp_weak_duality`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearProgramming.lp_weak_duality
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearProgramming.lp_weak_duality (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜)
    {x : Fin n → 𝕜} (hxA : ∀ i, b i ≤ ∑ j, A i j * x j) (hxnn : ∀ j, 0 ≤ x j)
    {u : I → 𝕜} (hu_du : DualFeasible A c u) :
    ∑ i, u i * b i ≤ ∑ j, c j * x j := by
  obtain ⟨hu_nn, hu_le⟩ := hu_du
  -- ⟨u, b⟩ ≤ ⟨u, A x⟩ (componentwise from Ax ≥ b, weighted by u ≥ 0)
  --        = ⟨uᵀA, x⟩
  --        ≤ ⟨c, x⟩      (componentwise from uᵀA ≤ c, weighted by x ≥ 0)
  calc ∑ i, u i * b i
      ≤ ∑ i, u i * (∑ j, A i j * x j) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hxA i) (hu_nn i)
    _ = ∑ j, (∑ i, u i * A i j) * x j := by
        have h1 : (∑ i, u i * ∑ j, A i j * x j)
            = ∑ i, ∑ j, u i * (A i j * x j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
        have h2 : (∑ i, ∑ j, u i * (A i j * x j))
            = ∑ j, ∑ i, u i * (A i j * x j) := Finset.sum_comm
        have h3 : (∑ j, ∑ i, u i * (A i j * x j))
            = ∑ j, (∑ i, u i * A i j) * x j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        rw [h1, h2, h3]
    _ ≤ ∑ j, c j * x j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hu_le j) (hxnn j)
