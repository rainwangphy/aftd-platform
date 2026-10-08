import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugB
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugRow
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInr

/-!
# EconCSLib.LinearProgramming.optAugB_inr

Topic: lp_duality   Node: ec49954a9ccd

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.optAugB_inr`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearProgramming.optAugB_inr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearProgramming.optAugB_inr (b : I → 𝕜) (v : 𝕜) :
    optAugB b v (Sum.inr () : OptAugRow I n) = -v := rfl
