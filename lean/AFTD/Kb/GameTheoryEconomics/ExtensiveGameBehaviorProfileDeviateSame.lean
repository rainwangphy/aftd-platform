import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileDeviate
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaToArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaInit
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGamePayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGameSelf
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaToArena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaInit
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaPayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsPlayerStateIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsNonPlayerStateIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameNoChanceIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsReachableIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtInit
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtPayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtNext
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtInit
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtPayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtNext
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# ExtensiveGame.BehaviorProfile.deviate_same

Topic: equilibria   Node: 0b223146da1f

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.deviate_same`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

ExtensiveGame.BehaviorProfile.deviate_same
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ExtensiveGame ExtensiveGame.BehaviorProfile in
variable {iota U : Type*} in
@[simp]
theorem ExtensiveGame.BehaviorProfile.deviate_same {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] [DecidableEq iota]
    (beta : G.BehaviorProfile) (who : iota) (beta' : G.BehaviorStrategy who) :
    beta.deviate who beta' who = beta' := by
  unfold ExtensiveGame.BehaviorProfile.deviate
  exact Function.update_self ..
