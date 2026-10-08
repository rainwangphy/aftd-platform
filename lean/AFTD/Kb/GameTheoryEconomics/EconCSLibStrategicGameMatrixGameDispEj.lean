import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMatrixGameDisp
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame

/-!
# EconCSLib.StrategicGame.MatrixGame.disp_Ej

Topic: equilibria   Node: 0f346f3e7f79

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.MatrixGame.disp_Ej`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Column-side payoff under `disp A`: `Ej x j = (xA)_j − x_j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- Column-side payoff under `disp A`: `Ej x j = (xA)_j − x_j`. -/
theorem EconCSLib.StrategicGame.MatrixGame.disp_Ej (A : I → I → ℝ) (x : stdSimplex ℝ I) (j : I) :
    (⟨disp A⟩ : MatrixGame I I ℝ).Ej x j
      = (∑ i, x.val i * A i j) - x.val j := by
  show wsum x (fun i => disp A i j) = (∑ i, x.val i * A i j) - x.val j
  show (∑ i, x.val i * (A i j - if i = j then 1 else 0))
      = (∑ i, x.val i * A i j) - x.val j
  rw [show (∑ i, x.val i * (A i j - if i = j then 1 else 0))
        = (∑ i, x.val i * A i j) - (∑ i, x.val i * (if i = j then 1 else 0)) from by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_); ring]
  congr 1
  show ∑ i, x.val i * (if i = j then (1 : ℝ) else 0) = x.val j
  simp [Fintype.sum_ite_eq', mul_ite]
