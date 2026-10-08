import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsStochasticMatrix
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsStochasticMatrix.total_mass_preserved

Topic: equilibria   Node: cadf877bdca3

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.IsStochasticMatrix.total_mass_preserved`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The total mass after one application of a stochastic matrix to a probability vector equals the initial mass: `∑_j (xA)_j = ∑_i x_i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
variable {A : I → I → ℝ} in
/-- The total mass after one application of a stochastic matrix to a probability vector equals the initial mass: `∑_j (xA)_j = ∑_i x_i`. -/
theorem EconCSLib.StrategicGame.IsStochasticMatrix.total_mass_preserved (hA : IsStochasticMatrix A) (x : I → ℝ) :
    ∑ j, ∑ i, x i * A i j = ∑ i, x i := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum, hA.rowSum, mul_one]
