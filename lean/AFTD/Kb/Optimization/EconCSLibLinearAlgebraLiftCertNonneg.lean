import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCert
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr

/-!
# EconCSLib.LinearAlgebra.liftCert_nonneg

Topic: lp_duality   Node: c93779319b1b

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCert_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise nonneg lift.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Pointwise nonneg lift. -/
theorem EconCSLib.LinearAlgebra.liftCert_nonneg (A : I → Fin (n+1) → 𝕜) {u' : FMRowIndex A → 𝕜}
    (hu' : ∀ idx, 0 ≤ u' idx) (i : I) : 0 ≤ liftCert A u' i := by
  apply Finset.sum_nonneg
  intro idx _
  apply mul_nonneg _ (hu' idx)
  rcases idx with k | ⟨p, q⟩
  · simp only [liftCoeff_inl]; split_ifs <;> norm_num
  · simp only [liftCoeff_inr]
    apply add_nonneg
    · split_ifs with hp
      · linarith [q.property]
      · norm_num
    · split_ifs with hq
      · exact p.property.le
      · norm_num
