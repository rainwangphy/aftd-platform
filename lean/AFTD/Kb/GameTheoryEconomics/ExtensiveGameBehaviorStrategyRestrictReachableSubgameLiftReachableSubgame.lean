import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyRestrictReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyLiftReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorStrategy.restrictReachableSubgame_liftReachableSubgame

Topic: equilibria   Node: b771e4df3d6b

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorStrategy.restrictReachableSubgame_liftReachableSubgame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.BehaviorStrategy.restrictReachableSubgame_liftReachableSubgame
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
@[simp]
theorem ExtensiveGame.BehaviorStrategy.restrictReachableSubgame_liftReachableSubgame
    {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota} {root : G.State}
    [(s : G.State) -> Decidable (Arena.Reachable G.toArena root s)]
    (base : G.BehaviorStrategy i)
    (beta : (G.reachableSubgameAt root).BehaviorStrategy i) :
    (base.liftReachableSubgame beta).restrictReachableSubgame root = beta := by
  funext s h hnonterminal
  cases s with
  | mk state hstate =>
      simp [restrictReachableSubgame, liftReachableSubgame, hstate]
