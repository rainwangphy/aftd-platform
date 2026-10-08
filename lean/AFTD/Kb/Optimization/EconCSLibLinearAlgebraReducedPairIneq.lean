import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl

/-!
# EconCSLib.LinearAlgebra.reduced_pair_ineq

Topic: lp_duality   Node: 8575979a5ab8

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.reduced_pair_ineq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.reduced_pair_ineq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearAlgebra.reduced_pair_ineq
    {A : I → Fin (n+1) → 𝕜} {b : I → 𝕜} {x' : Fin n → 𝕜}
    (hx' : ∀ idx, fmB A b idx ≤ rowEval (fmA A) idx x')
    (p : PosRows A) (q : NegRows A) :
    (b p.val - ∑ j : Fin n, A p.val j.castSucc * x' j) / A p.val (Fin.last n)
    ≤ (b q.val - ∑ j : Fin n, A q.val j.castSucc * x' j) / A q.val (Fin.last n) := by
  have h_pq := hx' (Sum.inr (p, q))
  simp only [fmB_inr, rowEval_def, fmA_inr] at h_pq
  -- Distribute the sum in h_pq's RHS.
  have hdist :
      (∑ j : Fin n,
        ((-A q.val (Fin.last n)) * A p.val j.castSucc
          + A p.val (Fin.last n) * A q.val j.castSucc) * x' j)
      = (-A q.val (Fin.last n))
          * (∑ j : Fin n, A p.val j.castSucc * x' j)
        + A p.val (Fin.last n)
          * (∑ j : Fin n, A q.val j.castSucc * x' j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hdist] at h_pq
  -- h_pq : (-A q last) · b p + A p last · b q ≤ (-A q last) · Σp + A p last · Σq
  have hβp : 0 < A p.val (Fin.last n) := p.property
  have hαq : 0 < -A q.val (Fin.last n) := by linarith [q.property]
  have hAql_neg : A q.val (Fin.last n) < 0 := q.property
  have hAql_ne : A q.val (Fin.last n) ≠ 0 := ne_of_lt hAql_neg
  -- Convert U_q's denominator (negative) to a positive form.
  set sumP := ∑ j : Fin n, A p.val j.castSucc * x' j with hsumP_def
  set sumQ := ∑ j : Fin n, A q.val j.castSucc * x' j with hsumQ_def
  have hUq_flip :
      (b q.val - sumQ) / A q.val (Fin.last n)
      = -(b q.val - sumQ) / (-A q.val (Fin.last n)) := by
    rw [neg_div_neg_eq]
  rw [hUq_flip]
  rw [div_le_div_iff₀ hβp hαq]
  -- Goal: (b p val - sumP) * (-A q val last) ≤ -(b q val - sumQ) * (A p val last)
  linarith
