import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameNashMap
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameNashMapAux
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameNashMapCert
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunction
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunctionCont
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameOneLeSumG

/-!
# EconCSLib.StrategicGame.nash_map_cont

Topic: equilibria   Node: 0569752a7eb8

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.nash_map_cont`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`nash_map G` is a continuous self-map of the product simplex.
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
/-- `nash_map G` is a continuous self-map of the product simplex. -/
theorem EconCSLib.StrategicGame.nash_map_cont : Continuous (nash_map G) := by
  unfold nash_map nash_map_aux
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_pi
  intro a
  apply Continuous.div
  · exact g_function_cont G i a
  · exact continuous_finset_sum _ fun b _ => g_function_cont G i b
  · intro σ
    exact ne_of_gt (lt_of_lt_of_le one_pos (one_le_sum_g G i σ))
