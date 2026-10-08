import AFTD.Prelude

/-!
# EconCSLib.LinearProgramming.OptAugRow

Topic: lp_duality   Node: 86607c5cde10

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.OptAugRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Optimality-augmented row index.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Optimality-augmented row index. -/
abbrev EconCSLib.LinearProgramming.OptAugRow (I : Type*) (n : ℕ) : Type _ := (I ⊕ Fin n) ⊕ Unit
