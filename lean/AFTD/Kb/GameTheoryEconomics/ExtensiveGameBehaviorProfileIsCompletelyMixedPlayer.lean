import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategyIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorProfile.IsCompletelyMixed.player

Topic: equilibria   Node: c533f5052013

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.IsCompletelyMixed.player`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A completely mixed behavior profile gives a completely mixed behavior strategy for each player.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- A completely mixed behavior profile gives a completely mixed behavior strategy for each player. -/
theorem ExtensiveGame.BehaviorProfile.IsCompletelyMixed.player {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {beta : G.BehaviorProfile}
    (hbeta : IsCompletelyMixed beta) (i : iota) :
    BehaviorStrategy.IsCompletelyMixed (G := G) (beta i) :=
  hbeta i
