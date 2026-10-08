import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl

/-!
# EconCSLib.LinearAlgebra.fmA_inr

Topic: lp_duality   Node: 56cbd1c2e85e

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.fmA_inr`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.fmA_inr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearAlgebra.fmA_inr (A : I → Fin (n+1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (j : Fin n) :
    fmA A (Sum.inr (p, q)) j
      = (-A q.val (Fin.last n)) * A p.val j.castSucc
        + A p.val (Fin.last n) * A q.val j.castSucc := rfl
