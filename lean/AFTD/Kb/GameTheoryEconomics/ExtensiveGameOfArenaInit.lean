import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaToArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaInit
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGamePayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGameSelf
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaToArena

/-!
# ExtensiveGame.ofArena_init

Topic: equilibria   Node: b12674241ca1

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ofArena_init`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.ofArena_init
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
@[simp]
theorem ExtensiveGame.ofArena_init (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N)
    (payoff : arena.State → N → U) :
    (ofArena arena init mover payoff).init = init :=
  rfl
