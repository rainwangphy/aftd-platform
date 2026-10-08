import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaToArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaMover
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaInit
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGameSelf
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGamePayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame

/-!
# ExtensiveGame.ofArena

Topic: equilibria   Node: 71a07fe9fe0b

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ofArena`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Add an initial state, mover assignment, and payoff function to an ordinary arena. All game-semantic data are explicit arguments; in particular this constructor does not infer chance nodes or terminal payoffs from the arena. It composes with observed-game presentation constructors without duplicating the arena's state, action, or transition fields.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- Add an initial state, mover assignment, and payoff function to an ordinary arena. All game-semantic data are explicit arguments; in particular this constructor does not infer chance nodes or terminal payoffs from the arena. It composes with observed-game presentation constructors without duplicating the arena's state, action, or transition fields. -/
abbrev ExtensiveGame.ofArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N)
    (payoff : arena.State → N → U) :
    ExtensiveGame N U :=
  ofControlledGame (ControlledGame.ofArena arena init mover) payoff
