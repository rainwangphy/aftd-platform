import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyRestrictReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame

/-!
# ExtensiveGame.BehaviorProfile.restrictReachableSubgame

Topic: equilibria   Node: aceb8c86cf64

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.restrictReachableSubgame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Restrict a behavior profile to the subtype subgame of states reachable from `root`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Restrict a behavior profile to the subtype subgame of states reachable from `root`. -/
def ExtensiveGame.BehaviorProfile.restrictReachableSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (root : G.State) :
    (G.reachableSubgameAt root).BehaviorProfile :=
  fun i => (beta i).restrictReachableSubgame root
