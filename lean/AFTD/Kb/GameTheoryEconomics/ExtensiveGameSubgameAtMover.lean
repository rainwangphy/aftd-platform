import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAt

/-!
# ExtensiveGame.subgameAt_mover

Topic: equilibria   Node: c3d11018b651

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.subgameAt_mover`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.subgameAt_mover
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
@[simp]
theorem ExtensiveGame.subgameAt_mover (G : ExtensiveGame iota U) (s t : G.State) :
    (G.subgameAt s).mover t = G.mover t := rfl
