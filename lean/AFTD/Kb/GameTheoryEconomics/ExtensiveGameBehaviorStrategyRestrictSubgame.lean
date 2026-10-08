import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAt
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorStrategy.restrictSubgame

Topic: equilibria   Node: c526ddaf1849

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorStrategy.restrictSubgame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Restrict a behavior strategy to the subgame rooted at `root`. Since `subgameAt` keeps the same state space, actions, and movers, this is just the same local action distribution viewed from the subgame.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Restrict a behavior strategy to the subgame rooted at `root`. Since `subgameAt` keeps the same state space, actions, and movers, this is just the same local action distribution viewed from the subgame. -/
def ExtensiveGame.BehaviorStrategy.restrictSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota}
    (beta : G.BehaviorStrategy i) (root : G.State) :
    (G.subgameAt root).BehaviorStrategy i :=
  fun s h hnonterminal => beta s h hnonterminal
