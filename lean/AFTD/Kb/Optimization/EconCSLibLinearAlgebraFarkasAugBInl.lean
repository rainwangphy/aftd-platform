import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugB

/-!
# EconCSLib.LinearAlgebra.farkasAugB_inl

Topic: lp_duality   Node: 17174569d936

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.farkasAugB_inl`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/Farkas.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.farkasAugB_inl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearAlgebra.farkasAugB_inl (b : I → 𝕜) (i : I) :
    farkasAugB b (Sum.inl i) = 0 := rfl
