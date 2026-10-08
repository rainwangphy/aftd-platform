import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGamePureToMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile

/-!
# EconCSLib.StrategicGame.pureProfileToMixed

Topic: equilibria   Node: dca747d83e8e

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.pureProfileToMixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Embed a pure profile as a mixed profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Embed a pure profile as a mixed profile. -/
def EconCSLib.StrategicGame.pureProfileToMixed {G : EconCSLib.StrategicGame N U}
    [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
    (σ : G.Profile) : MixedProfile G :=
  fun i => pureToMixed (σ i)
