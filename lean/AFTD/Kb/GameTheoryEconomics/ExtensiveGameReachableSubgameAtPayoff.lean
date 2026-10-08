import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAt
import AFTD.Kb.GameTheoryEconomics.ArenaReachable

/-!
# ExtensiveGame.reachableSubgameAt_payoff

Topic: equilibria   Node: ee87468d6b53

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.reachableSubgameAt_payoff`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Subgame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.reachableSubgameAt_payoff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
@[simp]
theorem ExtensiveGame.reachableSubgameAt_payoff (G : ExtensiveGame iota U) (root : G.State)
    (s : (G.reachableSubgameAt root).State) (i : iota) :
    (G.reachableSubgameAt root).payoff s i = G.payoff s.1 i := rfl
