import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCert
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCertWeightedSumSwap
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr

/-!
# EconCSLib.LinearAlgebra.liftCert_column_zero_last

Topic: lp_duality   Node: f0e5d9850155

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCert_column_zero_last`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lifted column-zero condition for `j = Fin.last n`: holds because the last column of `L · A` is zero by FM design.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Lifted column-zero condition for `j = Fin.last n`: holds because the last column of `L · A` is zero by FM design. -/
theorem EconCSLib.LinearAlgebra.liftCert_column_zero_last (A : I → Fin (n+1) → 𝕜)
    (u' : FMRowIndex A → 𝕜) :
    ∑ i, liftCert A u' i * A i (Fin.last n) = 0 := by
  rw [liftCert_weighted_sum_swap]
  apply Finset.sum_eq_zero
  intro idx _
  rcases idx with k | ⟨p, q⟩
  · simp only [liftCoeff_weighted_inl, k.property, mul_zero]
  · simp only [liftCoeff_weighted_inr]
    -- (-A q last) * A p last + A p last * A q last = 0
    ring
