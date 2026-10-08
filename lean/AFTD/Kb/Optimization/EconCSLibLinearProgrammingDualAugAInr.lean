import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugA
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingDualAugAInl

/-!
# EconCSLib.LinearProgramming.dualAugA_inr

Topic: lp_duality   Node: 7a8407714210

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.dualAugA_inr`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearProgramming.dualAugA_inr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearProgramming.dualAugA_inr (A : I → Fin n → 𝕜) (j' j : Fin n) :
    dualAugA A (Sum.inr j') j = if j = j' then 1 else 0 := rfl
