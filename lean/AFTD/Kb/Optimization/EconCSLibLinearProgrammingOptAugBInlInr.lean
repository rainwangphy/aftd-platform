import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugB
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugRow
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugBInlInl

/-!
# EconCSLib.LinearProgramming.optAugB_inl_inr

Topic: lp_duality   Node: eea2f47da6d8

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.optAugB_inl_inr`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearProgramming.optAugB_inl_inr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearProgramming.optAugB_inl_inr (b : I → 𝕜) (v : 𝕜) (j' : Fin n) :
    optAugB b v (Sum.inl (Sum.inr j') : OptAugRow I n) = 0 := rfl
