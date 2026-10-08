import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr

/-!
# EconCSLib.LinearAlgebra.liftCert

Topic: lp_duality   Node: 44014b3e94e8

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCert`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The lifted certificate `u i = ∑ idx, L idx i * u'(idx)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- The lifted certificate `u i = ∑ idx, L idx i * u'(idx)`. -/
def EconCSLib.LinearAlgebra.liftCert (A : I → Fin (n+1) → 𝕜) (u' : FMRowIndex A → 𝕜)
    (i : I) : 𝕜 :=
  ∑ idx, liftCoeff A idx i * u' idx
