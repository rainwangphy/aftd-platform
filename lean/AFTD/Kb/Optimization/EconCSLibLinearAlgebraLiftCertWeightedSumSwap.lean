import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCert
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex

/-!
# EconCSLib.LinearAlgebra.liftCert_weighted_sum_swap

Topic: lp_duality   Node: 7ede71ede792

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCert_weighted_sum_swap`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Inner-product-of-lift: `∑ i, liftCert u' i * g i = ∑ idx, u'(idx) * fmRow_at idx g`, where the `fmRow_at` value depends on `g` and `idx`. The lemma uses `Finset.sum_comm` to swap sums and `Finset.sum_ite_eq'` to evaluate the indicators. Specialised forms (`liftCert_weighted_A_castSucc`, `liftCert_weighted_A_last`, `liftCert_weighted_b`) recognise the inner sum as `fmA`/`0`/`fmB`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Inner-product-of-lift: `∑ i, liftCert u' i * g i = ∑ idx, u'(idx) * fmRow_at idx g`, where the `fmRow_at` value depends on `g` and `idx`. The lemma uses `Finset.sum_comm` to swap sums and `Finset.sum_ite_eq'` to evaluate the indicators. Specialised forms (`liftCert_weighted_A_castSucc`, `liftCert_weighted_A_last`, `liftCert_weighted_b`) recognise the inner sum as `fmA`/`0`/`fmB`. -/
theorem EconCSLib.LinearAlgebra.liftCert_weighted_sum_swap (A : I → Fin (n+1) → 𝕜)
    (u' : FMRowIndex A → 𝕜) (g : I → 𝕜) :
    ∑ i, liftCert A u' i * g i
    = ∑ idx, u' idx * (∑ i, liftCoeff A idx i * g i) := by
  unfold liftCert
  -- ∑ i, (∑ idx, L idx i * u' idx) * g i
  --   = ∑ i, ∑ idx, L idx i * u' idx * g i
  --   = ∑ idx, ∑ i, L idx i * u' idx * g i
  --   = ∑ idx, u' idx * (∑ i, L idx i * g i)
  rw [show (∑ i, (∑ idx, liftCoeff A idx i * u' idx) * g i)
      = ∑ i, ∑ idx, liftCoeff A idx i * u' idx * g i from ?_,
      Finset.sum_comm]
  · refine Finset.sum_congr rfl ?_
    intro idx _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]
