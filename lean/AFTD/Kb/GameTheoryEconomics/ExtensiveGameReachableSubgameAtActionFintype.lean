import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.reachableSubgameAt_action_fintype

Topic: equilibria   Node: 1b0f1a8a79e8

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.reachableSubgameAt_action_fintype`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.reachableSubgameAt_action_fintype
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
instance ExtensiveGame.reachableSubgameAt_action_fintype (G : ExtensiveGame iota U)
    (root : G.State) [inst : (s : G.State) -> Fintype (G.Action s)] :
    (s : (G.reachableSubgameAt root).State) ->
      Fintype ((G.reachableSubgameAt root).Action s) :=
  fun s => inst s.1
