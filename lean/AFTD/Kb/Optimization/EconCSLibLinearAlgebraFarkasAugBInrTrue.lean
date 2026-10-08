import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugBInrFalse

/-!
# EconCSLib.LinearAlgebra.farkasAugB_inr_true

Topic: lp_duality   Node: 5e26bffc454d

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.farkasAugB_inr_true`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/Farkas.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.farkasAugB_inr_true
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearAlgebra.farkasAugB_inr_true (b : I → 𝕜) :
    farkasAugB b (Sum.inr true) = 1 := rfl
