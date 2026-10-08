import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# EconCSLib.StrategicGame.IsCompletelyMixed

Topic: equilibria   Node: d47b42f70103

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsCompletelyMixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A player's mixed strategy is completely mixed if every pure strategy is assigned positive probability. This is the strategic-form mixed-strategy part of MSZ Definition 7.6.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- A player's mixed strategy is completely mixed if every pure strategy is assigned positive probability. This is the strategic-form mixed-strategy part of MSZ Definition 7.6. -/
def EconCSLib.StrategicGame.IsCompletelyMixed
    (G : EconCSLib.StrategicGame N ℚ) {i : N} [Fintype (G.strategy i)]
    (p : MixedStrategy G i) : Prop :=
  ∀ s : G.strategy i, 0 < p.val s
