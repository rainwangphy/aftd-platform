import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameExpectedPayoff
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviateMixed
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.IsMixedNashEq

Topic: equilibria   Node: bcdc031e5d42

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsMixedNashEq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A mixed profile is a mixed Nash equilibrium if no player can improve their expected payoff by deviating to any pure strategy. By linearity of expected payoff in each player's mixed strategy, checking pure deviations suffices. [MSZ 5.5, 5.18] Requires `[Fintype N]` for expected payoff computation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- A mixed profile is a mixed Nash equilibrium if no player can improve their expected payoff by deviating to any pure strategy. By linearity of expected payoff in each player's mixed strategy, checking pure deviations suffices. [MSZ 5.5, 5.18] Requires `[Fintype N]` for expected payoff computation. -/
def EconCSLib.StrategicGame.IsMixedNashEq
    (G : EconCSLib.StrategicGame N U)
    [Fintype N] [DecidableEq N]
    [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
    (p : MixedProfile G) : Prop :=
  ∀ (who : N) (s' : G.strategy who),
    expectedPayoff G (deviateMixed G p who s') who ≤
    expectedPayoff G p who
