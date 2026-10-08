import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex

/-!
# EconCSLib.LinearAlgebra.liftCoeff

Topic: lp_duality   Node: 53414460c859

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.liftCoeff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The FM lift coefficient `L idx i`: the weight with which original row `i` enters the reduced row `idx`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- The FM lift coefficient `L idx i`: the weight with which original row `i` enters the reduced row `idx`. -/
def EconCSLib.LinearAlgebra.liftCoeff (A : I → Fin (n+1) → 𝕜) (idx : FMRowIndex A) (i : I) : 𝕜 :=
  match idx with
  | Sum.inl k => if k.val = i then 1 else 0
  | Sum.inr (p, q) =>
      (if p.val = i then -A q.val (Fin.last n) else 0)
      + (if q.val = i then A p.val (Fin.last n) else 0)
