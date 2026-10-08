import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAt
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyRestrictSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyLiftSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorStrategy.restrictSubgame_liftSubgame

Topic: equilibria   Node: 24ef9227dbdc

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorStrategy.restrictSubgame_liftSubgame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.BehaviorStrategy.restrictSubgame_liftSubgame
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
@[simp]
theorem ExtensiveGame.BehaviorStrategy.restrictSubgame_liftSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota} {root : G.State}
    (beta : (G.subgameAt root).BehaviorStrategy i) :
    beta.liftSubgame.restrictSubgame root = beta := by
  funext s h hnonterminal
  rfl
