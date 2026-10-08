import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIdMat
import AFTD.Kb.Optimization.WsumPureApply

/-!
# EconCSLib.LinearAlgebra.xA_idMat

Topic: lp_duality   Node: c250c008207b

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.xA_idMat`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/PerronFrobenius.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.xA_idMat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Loomis in
set_option linter.unusedSectionVars false in
variable {n : ℕ} [NeZero n] in
theorem EconCSLib.LinearAlgebra.xA_idMat (x : stdSimplex ℝ (Fin n)) (j : Fin n) :
    Loomis.xA idMat x j = x.val j := by
  classical
  show ∑ i, x.val i * (if i = j then (1 : ℝ) else 0) = x.val j
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']
