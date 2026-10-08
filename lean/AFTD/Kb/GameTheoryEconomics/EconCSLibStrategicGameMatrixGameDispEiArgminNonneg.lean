import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsStochasticMatrix
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMatrixGameDisp
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMatrixGameDispEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame

/-!
# EconCSLib.StrategicGame.MatrixGame.disp_Ei_argmin_nonneg

Topic: equilibria   Node: a09aa99d272c

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.MatrixGame.disp_Ei_argmin_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For any column-player strategy `y`, picking the index where `y` is minimal gives a non-negative row payoff under `disp A`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- For any column-player strategy `y`, picking the index where `y` is minimal gives a non-negative row payoff under `disp A`. -/
theorem EconCSLib.StrategicGame.MatrixGame.disp_Ei_argmin_nonneg (A : I → I → ℝ) (hA : IsStochasticMatrix A)
    (y : stdSimplex ℝ I) :
    ∃ i, 0 ≤ (⟨disp A⟩ : MatrixGame I I ℝ).Ei i y := by
  -- Pick i₀ = argmin_j y.val j.
  obtain ⟨i₀, _, hi_min⟩ := Finset.exists_min_image Finset.univ y.val Finset.univ_nonempty
  -- hi_min : ∀ i ∈ univ, y.val i₀ ≤ y.val i.
  refine ⟨i₀, ?_⟩
  rw [disp_Ei A y i₀]
  -- (Ay)_{i₀} ≥ y_{i₀} via A_{i₀,j} ≥ 0, y_j ≥ y_{i₀}, ∑ A_{i₀,j} = 1.
  have hAy_ge : ∑ j, A i₀ j * y.val j ≥ y.val i₀ := by
    have hge : ∀ j, A i₀ j * y.val i₀ ≤ A i₀ j * y.val j := fun j =>
      mul_le_mul_of_nonneg_left (hi_min j (Finset.mem_univ _)) (hA.nonneg i₀ j)
    calc y.val i₀
        = (∑ j, A i₀ j) * y.val i₀ := by rw [hA.rowSum i₀, one_mul]
      _ = ∑ j, A i₀ j * y.val i₀ := by rw [Finset.sum_mul]
      _ ≤ ∑ j, A i₀ j * y.val j := Finset.sum_le_sum (fun j _ => hge j)
  linarith
