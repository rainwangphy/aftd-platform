import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef

/-!
# EconCSLib.LinearAlgebra.fm_feasible_of_feasible

Topic: lp_duality   Node: 7917ae93fd1c

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.fm_feasible_of_feasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.fm_feasible_of_feasible
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearAlgebra.fm_feasible_of_feasible (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (hfeas : IsFeasible A b) : IsFeasible (fmA A) (fmB A b) := by
  obtain ⟨x, hx⟩ := hfeas
  refine ⟨fun j => x j.castSucc, ?_⟩
  intro idx
  -- Split each original row sum into first n + last entry.
  have hsplit : ∀ i : I,
      rowEval A i x
        = (∑ j : Fin n, A i j.castSucc * x j.castSucc)
          + A i (Fin.last n) * x (Fin.last n) := by
    intro i
    rw [rowEval, Fin.sum_univ_castSucc]
  rcases idx with k | ⟨p, q⟩
  · -- Zero-row pass-through.
    have hk := hx k.val
    rw [hsplit, k.property, zero_mul, add_zero] at hk
    simp only [fmB_inl, rowEval_def, fmA_inl]
    exact hk
  · -- Combined-row inequality.
    have hp := hx p.val
    have hq := hx q.val
    rw [hsplit] at hp hq
    have hαq_pos : 0 < -A q.val (Fin.last n) := by linarith [q.property]
    have hβp_pos : 0 < A p.val (Fin.last n) := p.property
    -- αq · (hp stripped) + βp · (hq stripped) gives the combined inequality.
    have hcomb :
        (-A q.val (Fin.last n)) * b p.val
          + A p.val (Fin.last n) * b q.val
        ≤ (-A q.val (Fin.last n))
            * (∑ j : Fin n, A p.val j.castSucc * x j.castSucc)
          + A p.val (Fin.last n)
            * (∑ j : Fin n, A q.val j.castSucc * x j.castSucc) := by
      have hp_strip :
          b p.val - A p.val (Fin.last n) * x (Fin.last n)
          ≤ ∑ j : Fin n, A p.val j.castSucc * x j.castSucc := by linarith
      have hq_strip :
          b q.val - A q.val (Fin.last n) * x (Fin.last n)
          ≤ ∑ j : Fin n, A q.val j.castSucc * x j.castSucc := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hp_strip hαq_pos.le,
        mul_le_mul_of_nonneg_left hq_strip hβp_pos.le]
    simp only [fmB_inr, rowEval_def, fmA_inr]
    -- Distribute the sum in the goal RHS.
    have hRHS :
        (∑ j : Fin n,
          ((-A q.val (Fin.last n)) * A p.val j.castSucc
            + A p.val (Fin.last n) * A q.val j.castSucc)
            * x j.castSucc)
        = (-A q.val (Fin.last n))
            * (∑ j : Fin n, A p.val j.castSucc * x j.castSucc)
          + A p.val (Fin.last n)
            * (∑ j : Fin n, A q.val j.castSucc * x j.castSucc) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hRHS]
    exact hcomb
