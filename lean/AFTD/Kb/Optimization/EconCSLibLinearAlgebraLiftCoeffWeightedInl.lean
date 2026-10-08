import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Tcs.G

/-!
# EconCSLib.LinearAlgebra.liftCoeff_weighted_inl

Topic: lp_duality   Node: 67077b9a2828

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCoeff_weighted_inl`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Inner sum at `Sum.inl k` collapses to the picked-out row: `∑ i, L (inl k) i * g i = g k.val`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Inner sum at `Sum.inl k` collapses to the picked-out row: `∑ i, L (inl k) i * g i = g k.val`. -/
@[simp] theorem EconCSLib.LinearAlgebra.liftCoeff_weighted_inl (A : I → Fin (n+1) → 𝕜)
    (k : ZeroRows A) (g : I → 𝕜) :
    ∑ i, liftCoeff A (Sum.inl k) i * g i = g k.val := by
  classical
  simp only [liftCoeff_inl, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
