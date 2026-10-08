import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeff
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr

/-!
# EconCSLib.LinearAlgebra.liftCoeff_inr

Topic: lp_duality   Node: 17e620f8269d

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCoeff_inr`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.liftCoeff_inr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearAlgebra.liftCoeff_inr (A : I → Fin (n+1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (i : I) :
    liftCoeff A (Sum.inr (p, q)) i
      = (if p.val = i then -A q.val (Fin.last n) else 0)
        + (if q.val = i then A p.val (Fin.last n) else 0) := rfl
