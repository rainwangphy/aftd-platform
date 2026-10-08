import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugRow

/-!
# EconCSLib.LinearProgramming.optAugB

Topic: lp_duality   Node: fae41f249ac0

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.optAugB`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Optimality-augmented RHS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Optimality-augmented RHS. -/
def EconCSLib.LinearProgramming.optAugB (b : I → 𝕜) (v : 𝕜) : OptAugRow I n → 𝕜
  | Sum.inl (Sum.inl i) => b i
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr () => -v
