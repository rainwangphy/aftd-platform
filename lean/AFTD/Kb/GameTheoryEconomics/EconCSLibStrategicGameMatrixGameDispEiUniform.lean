import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsStochasticMatrix
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMatrixGameDisp
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformDistVal
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformDist
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMatrixGameDispEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame

/-!
# EconCSLib.StrategicGame.MatrixGame.disp_Ei_uniform

Topic: equilibria   Node: 604b831b54bd

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.MatrixGame.disp_Ei_uniform`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Under the uniform distribution, the column-side payoff under `disp A` is zero (when `A` is stochastic).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- Under the uniform distribution, the column-side payoff under `disp A` is zero (when `A` is stochastic). -/
theorem EconCSLib.StrategicGame.MatrixGame.disp_Ei_uniform (A : I → I → ℝ) (hA : IsStochasticMatrix A) (i : I) :
    (⟨disp A⟩ : MatrixGame I I ℝ).Ei i (uniformDist : stdSimplex ℝ I) = 0 := by
  rw [disp_Ei A uniformDist i]
  simp only [uniformDist_val]
  -- ∑ j, A i j * (1/n) - 1/n = (1/n)·(∑ A i j) - 1/n = 1/n - 1/n = 0.
  have hcard_pos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hne : (Fintype.card I : ℝ) ≠ 0 := hcard_pos.ne'
  have hsum : (∑ j, A i j * (1 / (Fintype.card I : ℝ)))
            = (∑ j, A i j) / (Fintype.card I : ℝ) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hsum, hA.rowSum]; ring
