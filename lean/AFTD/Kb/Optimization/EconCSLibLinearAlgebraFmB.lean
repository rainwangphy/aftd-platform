import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex

/-!
# EconCSLib.LinearAlgebra.fmB

Topic: lp_duality   Node: b0dc7830f212

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.fmB`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reduced right-hand side.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Reduced right-hand side. -/
def EconCSLib.LinearAlgebra.fmB (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜) (idx : FMRowIndex A) : 𝕜 :=
  match idx with
  | Sum.inl k => b k.val
  | Sum.inr ⟨p, q⟩ =>
      (-A q.val (Fin.last n)) * b p.val
        + A p.val (Fin.last n) * b q.val
