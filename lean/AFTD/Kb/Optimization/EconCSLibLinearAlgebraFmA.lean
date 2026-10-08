import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows

/-!
# EconCSLib.LinearAlgebra.fmA

Topic: lp_duality   Node: 8ced8032693b

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.fmA`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reduced matrix coefficient.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Reduced matrix coefficient. -/
def EconCSLib.LinearAlgebra.fmA (A : I → Fin (n+1) → 𝕜) (idx : FMRowIndex A) (j : Fin n) : 𝕜 :=
  match idx with
  | Sum.inl k => A k.val j.castSucc
  | Sum.inr ⟨p, q⟩ =>
      (-A q.val (Fin.last n)) * A p.val j.castSucc
        + A p.val (Fin.last n) * A q.val j.castSucc
