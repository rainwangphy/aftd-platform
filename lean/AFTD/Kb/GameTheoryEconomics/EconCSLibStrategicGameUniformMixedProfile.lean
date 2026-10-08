import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile

/-!
# EconCSLib.StrategicGame.uniformMixedProfile

Topic: equilibria   Node: 3decaf7f5bfe

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.uniformMixedProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The profile where every player uses the uniform mixed strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- The profile where every player uses the uniform mixed strategy. -/
def EconCSLib.StrategicGame.uniformMixedProfile
    (G : EconCSLib.StrategicGame N ℚ) [∀ i, Fintype (G.strategy i)]
    [∀ i, Nonempty (G.strategy i)] : MixedProfile G :=
  fun i => uniformMixed (G := G) (i := i)
