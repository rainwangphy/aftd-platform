import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsCompletelyMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.IsCompletelyMixedProfile.player

Topic: equilibria   Node: 08193ff14482

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsCompletelyMixedProfile.player`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A completely mixed profile gives a completely mixed strategy for each player.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- A completely mixed profile gives a completely mixed strategy for each player. -/
theorem EconCSLib.StrategicGame.IsCompletelyMixedProfile.player {G : EconCSLib.StrategicGame N ℚ}
    [∀ i, Fintype (G.strategy i)] {p : MixedProfile G}
    (hp : IsCompletelyMixedProfile G p) (i : N) :
    IsCompletelyMixed G (p i) :=
  hp i
