import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAt

/-!
# ExtensiveGame.subgameAt_next

Topic: equilibria   Node: 3c6d41d5ce76

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.subgameAt_next`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.subgameAt_next
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
@[simp]
theorem ExtensiveGame.subgameAt_next (G : ExtensiveGame iota U) (s t : G.State)
    (a : G.Action t) :
    (G.subgameAt s).next t a = G.next t a := rfl
