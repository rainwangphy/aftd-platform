import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugRow
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrFalseCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrFalseLast
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInlCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInlLast
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrTrueCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFarkasAugAInrTrueLast

/-!
# EconCSLib.LinearAlgebra.augRowEval_inr_false

Topic: lp_duality   Node: baf503a73bb3

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.augRowEval_inr_false`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/Farkas.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.augRowEval_inr_false
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearAlgebra.augRowEval_inr_false
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (d : 𝕜)
    (xt : Fin (n+1) → 𝕜) :
    rowEval (farkasAugA A b c d) (Sum.inr false) xt = xt (Fin.last n) := by
  rw [rowEval, Fin.sum_univ_castSucc]
  simp only [farkasAugA_inr_false_castSucc, farkasAugA_inr_false_last, zero_mul,
             Finset.sum_const_zero, zero_add, one_mul]
