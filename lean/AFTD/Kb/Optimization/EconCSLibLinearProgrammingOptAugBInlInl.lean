import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugB
import AFTD.Kb.Optimization.EconCSLibLinearProgrammingOptAugRow

/-!
# EconCSLib.LinearProgramming.optAugB_inl_inl

Topic: lp_duality   Node: c0b0ce51c97c

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.optAugB_inl_inl`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongComplementarity.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearProgramming.optAugB_inl_inl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearProgramming.optAugB_inl_inl (b : I → 𝕜) (v : 𝕜) (i : I) :
    optAugB b v (Sum.inl (Sum.inl i) : OptAugRow I n) = b i := rfl
