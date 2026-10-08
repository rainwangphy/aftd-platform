import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugA
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInl
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugAInlInr

/-!
# EconCSLib.LinearProgramming.optAugA_inr

Topic: lp_duality   Node: 152fc2abb12c

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.optAugA_inr`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearProgramming.optAugA_inr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearProgramming.optAugA_inr (A : I → Fin n → 𝕜) (c : Fin n → 𝕜) (j : Fin n) :
    optAugA A c (Sum.inr ()) j = -c j := rfl
