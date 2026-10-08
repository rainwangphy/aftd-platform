import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCert
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCertWeightedSumSwap
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr

/-!
# EconCSLib.LinearAlgebra.liftCert_column_zero_castSucc

Topic: lp_duality   Node: f00ed83a6b93

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCert_column_zero_castSucc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lifted column-zero condition for `j ∈ Fin n`: matches `fmA A · j = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Lifted column-zero condition for `j ∈ Fin n`: matches `fmA A · j = 0`. -/
theorem EconCSLib.LinearAlgebra.liftCert_column_zero_castSucc (A : I → Fin (n+1) → 𝕜)
    (b : I → 𝕜) {u' : FMRowIndex A → 𝕜}
    (hu'_zero : ∀ j : Fin n, ∑ idx, u' idx * fmA A idx j = 0) (j : Fin n) :
    ∑ i, liftCert A u' i * A i j.castSucc = 0 := by
  rw [liftCert_weighted_sum_swap]
  -- ∑ idx, u' idx * (∑ i, L idx i * A i j.castSucc) = ∑ idx, u' idx * fmA A idx j
  have : ∀ idx, ∑ i, liftCoeff A idx i * A i j.castSucc = fmA A idx j := by
    intro idx
    rcases idx with k | ⟨p, q⟩
    · simp [liftCoeff_weighted_inl]
    · simp [liftCoeff_weighted_inr]
  simp_rw [this]
  exact hu'_zero j
