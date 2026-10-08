import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGamePureToMixed
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.deviateMixed

Topic: equilibria   Node: 3808a8f201ce

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.deviateMixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Deviate player `who` to pure strategy `s'`, keeping others' mixed strategies.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Deviate player `who` to pure strategy `s'`, keeping others' mixed strategies. -/
def EconCSLib.StrategicGame.deviateMixed
    (G : EconCSLib.StrategicGame N U)
    [∀ i, Fintype (G.strategy i)] [DecidableEq N] [∀ i, DecidableEq (G.strategy i)]
    (p : MixedProfile G) (who : N) (s' : G.strategy who) : MixedProfile G :=
  Function.update p who (pureToMixed s')
