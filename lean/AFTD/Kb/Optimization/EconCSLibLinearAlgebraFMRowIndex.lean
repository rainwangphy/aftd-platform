import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows

/-!
# EconCSLib.LinearAlgebra.FMRowIndex

Topic: lp_duality   Node: ee43103840a5

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.FMRowIndex`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reduced row index after Fourier-Motzkin elimination of the last column.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Reduced row index after Fourier-Motzkin elimination of the last column. -/
abbrev EconCSLib.LinearAlgebra.FMRowIndex (A : I → Fin (n+1) → 𝕜) : Type _ :=
  ZeroRows A ⊕ (PosRows A × NegRows A)
