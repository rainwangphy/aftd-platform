import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.IsCompletelyMixedProfile

Topic: equilibria   Node: 5f1af8b928e2

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsCompletelyMixedProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A mixed profile is completely mixed if every player's mixed strategy is completely mixed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- A mixed profile is completely mixed if every player's mixed strategy is completely mixed. -/
def EconCSLib.StrategicGame.IsCompletelyMixedProfile
    (G : EconCSLib.StrategicGame N ℚ) [∀ i, Fintype (G.strategy i)]
    (p : MixedProfile G) : Prop :=
  ∀ i : N, IsCompletelyMixed G (p i)
