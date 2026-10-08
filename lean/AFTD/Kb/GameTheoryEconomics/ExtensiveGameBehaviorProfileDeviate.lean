import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame

/-!
# ExtensiveGame.BehaviorProfile.deviate

Topic: equilibria   Node: 4f3d339cad8e

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.deviate`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unilateral deviation of a behavior profile: player `who` switches to `beta'`, while every other player keeps the original behavior strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Unilateral deviation of a behavior profile: player `who` switches to `beta'`, while every other player keeps the original behavior strategy. -/
def ExtensiveGame.BehaviorProfile.deviate {G : ExtensiveGame iota U} [(s : G.State) -> Fintype (G.Action s)]
    [DecidableEq iota] (beta : G.BehaviorProfile) (who : iota)
    (beta' : G.BehaviorStrategy who) : G.BehaviorProfile :=
  Function.update beta who beta'
