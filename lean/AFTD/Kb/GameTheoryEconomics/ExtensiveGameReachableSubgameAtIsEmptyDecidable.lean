import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype

/-!
# ExtensiveGame.reachableSubgameAt_isEmpty_decidable

Topic: equilibria   Node: c29f6c2e2b87

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.reachableSubgameAt_isEmpty_decidable`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.reachableSubgameAt_isEmpty_decidable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
instance ExtensiveGame.reachableSubgameAt_isEmpty_decidable (G : ExtensiveGame iota U)
    (root : G.State)
    [inst : (s : G.State) -> Decidable (IsEmpty (G.Action s))] :
    (s : (G.reachableSubgameAt root).State) ->
      Decidable (IsEmpty ((G.reachableSubgameAt root).Action s)) :=
  fun s => inst s.1
