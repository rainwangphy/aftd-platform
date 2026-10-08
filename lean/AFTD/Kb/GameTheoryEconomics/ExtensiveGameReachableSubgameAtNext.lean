import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ArenaReachableStep'

/-!
# ExtensiveGame.reachableSubgameAt_next

Topic: equilibria   Node: 08974adc9176

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.reachableSubgameAt_next`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Subgame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.reachableSubgameAt_next
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
@[simp]
theorem ExtensiveGame.reachableSubgameAt_next (G : ExtensiveGame iota U) (root : G.State)
    (s : (G.reachableSubgameAt root).State)
    (a : (G.reachableSubgameAt root).Action s) :
    (G.reachableSubgameAt root).next s a = ⟨G.next s.1 a, s.2.step' a⟩ := rfl
