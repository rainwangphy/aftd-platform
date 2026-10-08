import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInlCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInlLast
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrFalseCastSucc

/-!
# EconCSLib.LinearAlgebra.farkasAugA_inr_false_last

Topic: lp_duality   Node: cb79386ec02b

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.farkasAugA_inr_false_last`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/Farkas.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.farkasAugA_inr_false_last
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
@[simp] theorem EconCSLib.LinearAlgebra.farkasAugA_inr_false_last (A : I → Fin n → 𝕜) (b : I → 𝕜)
    (c : Fin n → 𝕜) (d : 𝕜) :
    farkasAugA A b c d (Sum.inr false) (Fin.last n) = 1 := by
  simp [farkasAugA]
