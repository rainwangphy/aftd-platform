import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMatrixGameDisp
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.MatrixGame.disp_Ei

Topic: equilibria   Node: c706709ccd9d

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.MatrixGame.disp_Ei`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Row-side payoff under `disp A`: `Ei i y = (Ay)_i − y_i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- Row-side payoff under `disp A`: `Ei i y = (Ay)_i − y_i`. -/
theorem EconCSLib.StrategicGame.MatrixGame.disp_Ei (A : I → I → ℝ) (y : stdSimplex ℝ I) (i : I) :
    (⟨disp A⟩ : MatrixGame I I ℝ).Ei i y
      = (∑ j, A i j * y.val j) - y.val i := by
  show wsum y (fun j => disp A i j) = (∑ j, A i j * y.val j) - y.val i
  show (∑ j, y.val j * (A i j - if i = j then 1 else 0))
      = (∑ j, A i j * y.val j) - y.val i
  rw [show (∑ j, y.val j * (A i j - if i = j then 1 else 0))
        = (∑ j, y.val j * A i j) - (∑ j, y.val j * (if i = j then 1 else 0)) from by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun j _ => ?_); ring]
  rw [show (∑ j, y.val j * A i j) = ∑ j, A i j * y.val j from
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)]
  congr 1
  show ∑ j, y.val j * (if i = j then (1 : ℝ) else 0) = y.val i
  simp [Fintype.sum_ite_eq, mul_ite]
