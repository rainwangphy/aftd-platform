import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugRow

/-!
# EconCSLib.LinearProgramming.dualAugA

Topic: lp_duality   Node: 909b83a4f456

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.dualAugA`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Augmented matrix combining `A` rows with `x ≥ 0` unit rows.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Augmented matrix combining `A` rows with `x ≥ 0` unit rows. -/
def EconCSLib.LinearProgramming.dualAugA (A : I → Fin n → 𝕜) : DualAugRow I n → Fin n → 𝕜
  | Sum.inl i, j => A i j
  | Sum.inr j', j => if j = j' then 1 else 0
