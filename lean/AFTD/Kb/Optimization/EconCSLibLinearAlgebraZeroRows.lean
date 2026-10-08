import AFTD.Prelude

/-!
# EconCSLib.LinearAlgebra.ZeroRows

Topic: lp_duality   Node: 9b3f433ffb16

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.ZeroRows`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rows where the last-column coefficient is zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Rows where the last-column coefficient is zero. -/
abbrev EconCSLib.LinearAlgebra.ZeroRows (A : I → Fin (n+1) → 𝕜) : Type _ :=
  { i : I // A i (Fin.last n) = 0 }
