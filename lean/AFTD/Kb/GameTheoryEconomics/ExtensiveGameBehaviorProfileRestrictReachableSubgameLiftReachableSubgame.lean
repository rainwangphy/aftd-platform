import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileRestrictReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileLiftReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyRestrictReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyLiftReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyRestrictReachableSubgameLiftReachableSubgame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorProfile.restrictReachableSubgame_liftReachableSubgame

Topic: equilibria   Node: a7fa18316cea

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.restrictReachableSubgame_liftReachableSubgame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.BehaviorProfile.restrictReachableSubgame_liftReachableSubgame
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
@[simp]
theorem ExtensiveGame.BehaviorProfile.restrictReachableSubgame_liftReachableSubgame
    {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {root : G.State}
    [(s : G.State) -> Decidable (Arena.Reachable G.toArena root s)]
    (base : G.BehaviorProfile)
    (beta : (G.reachableSubgameAt root).BehaviorProfile) :
    (base.liftReachableSubgame beta).restrictReachableSubgame root = beta := by
  funext i s h hnonterminal
  simp [restrictReachableSubgame, liftReachableSubgame]
