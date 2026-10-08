import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorStrategy.restrictReachableSubgame

Topic: equilibria   Node: 0b1f8dd7ad92

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorStrategy.restrictReachableSubgame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Restrict a behavior strategy to the subtype subgame consisting only of states reachable from `root`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Restrict a behavior strategy to the subtype subgame consisting only of states reachable from `root`. -/
def ExtensiveGame.BehaviorStrategy.restrictReachableSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota}
    (beta : G.BehaviorStrategy i) (root : G.State) :
    (G.reachableSubgameAt root).BehaviorStrategy i :=
  fun s h hnonterminal => beta s.1 h hnonterminal
