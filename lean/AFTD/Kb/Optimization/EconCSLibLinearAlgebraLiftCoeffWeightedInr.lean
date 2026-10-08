import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInl
import AFTD.Kb.Tcs.G

/-!
# EconCSLib.LinearAlgebra.liftCoeff_weighted_inr

Topic: lp_duality   Node: f6b1fba826b5

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCoeff_weighted_inr`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Inner sum at `Sum.inr (p, q)` collapses to the combined row contributions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Inner sum at `Sum.inr (p, q)` collapses to the combined row contributions. -/
@[simp] theorem EconCSLib.LinearAlgebra.liftCoeff_weighted_inr (A : I → Fin (n+1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (g : I → 𝕜) :
    ∑ i, liftCoeff A (Sum.inr (p, q)) i * g i
    = (-A q.val (Fin.last n)) * g p.val + A p.val (Fin.last n) * g q.val := by
  classical
  simp only [liftCoeff_inr, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
             Fintype.sum_ite_eq]
