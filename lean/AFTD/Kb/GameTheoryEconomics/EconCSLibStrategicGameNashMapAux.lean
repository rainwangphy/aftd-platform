import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunction
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.Tcs.Weight

/-!
# EconCSLib.StrategicGame.nash_map_aux

Topic: equilibria   Node: 77fb99a93ae5

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.nash_map_aux`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normalized augmented weight: `g_function i σ a / ∑_b g_function i σ b`. Private auxiliary used to construct `nash_map`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Function in
set_option linter.unusedSectionVars false in
variable {N : Type*} in
variable (G : EconCSLib.StrategicGame N ℝ) in
variable [Fintype N] [DecidableEq N] in
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)] in
variable [∀ i, Inhabited (G.strategy i)] in
/-- The normalized augmented weight: `g_function i σ a / ∑_b g_function i σ b`. Private auxiliary used to construct `nash_map`. -/
noncomputable def EconCSLib.StrategicGame.nash_map_aux (σ : MixedS G) (i : N) (a : G.strategy i) : ℝ :=
  g_function G i σ a / ∑ b : G.strategy i, g_function G i σ b
