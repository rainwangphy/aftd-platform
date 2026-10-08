import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval

/-!
# EconCSLib.LinearAlgebra.rowEval_def

Topic: lp_duality   Node: 8d3fcdb56bc3

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.rowEval_def`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.rowEval_def
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearAlgebra.rowEval_def {I : Type*} {n : ℕ} [Fintype I]
    (A : I → Fin n → 𝕜) (i : I) (x : Fin n → 𝕜) :
    rowEval A i x = ∑ j, A i j * x j := rfl
