import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIdMat
import AFTD.Kb.Optimization.WsumPureApply

/-!
# EconCSLib.LinearAlgebra.Ay_idMat

Topic: lp_duality   Node: f65d00ff6064

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.Ay_idMat`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/PerronFrobenius.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.Ay_idMat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Loomis in
set_option linter.unusedSectionVars false in
variable {n : ℕ} [NeZero n] in
theorem EconCSLib.LinearAlgebra.Ay_idMat (y : stdSimplex ℝ (Fin n)) (i : Fin n) :
    Loomis.Ay idMat y i = y.val i := by
  classical
  show ∑ j, y.val j * (if i = j then (1 : ℝ) else 0) = y.val i
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
