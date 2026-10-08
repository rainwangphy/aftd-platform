import AFTD.Prelude

/-!
# EconCSLib.LinearProgramming.DualAugRow

Topic: lp_duality   Node: 0432c6dcc562

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.DualAugRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Augmented row index for the LP-Farkas reduction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Augmented row index for the LP-Farkas reduction. -/
abbrev EconCSLib.LinearProgramming.DualAugRow (I : Type*) (n : ℕ) : Type _ := I ⊕ Fin n
