import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunction
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameSigmaLeGFunction
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.Tcs.Weight

/-!
# EconCSLib.StrategicGame.g_function_nonneg

Topic: equilibria   Node: 1de8d037ee88

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.g_function_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The augmented weight is nonnegative.
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
/-- The augmented weight is nonnegative. -/
lemma EconCSLib.StrategicGame.g_function_nonneg (i : N) (σ : MixedS G) (a : G.strategy i) :
    0 ≤ g_function G i σ a := by
  have h1 : 0 ≤ (σ i).val a := (σ i).property.1 a
  linarith [sigma_le_g_function G i σ a]
