import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCert
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCertWeightedSumSwap
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr

/-!
# EconCSLib.LinearAlgebra.liftCert_rhs

Topic: lp_duality   Node: 980cf59a5ea7

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCert_rhs`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lifted RHS-positivity: matches `∑ idx, u' idx * fmB idx > 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Lifted RHS-positivity: matches `∑ idx, u' idx * fmB idx > 0`. -/
theorem EconCSLib.LinearAlgebra.liftCert_rhs (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (u' : FMRowIndex A → 𝕜) :
    ∑ i, liftCert A u' i * b i = ∑ idx, u' idx * fmB A b idx := by
  rw [liftCert_weighted_sum_swap]
  refine Finset.sum_congr rfl ?_
  intro idx _
  rcases idx with k | ⟨p, q⟩
  · simp [liftCoeff_weighted_inl]
  · simp [liftCoeff_weighted_inr]
