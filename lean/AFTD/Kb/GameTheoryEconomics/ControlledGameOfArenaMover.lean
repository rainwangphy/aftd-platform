import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaToArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaInit

/-!
# ControlledGame.ofArena_mover

Topic: equilibria   Node: 45665a637d80

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.ofArena_mover`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ControlledGame.ofArena_mover
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
@[simp]
theorem ControlledGame.ofArena_mover (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) (state : arena.State) :
    (ofArena arena init mover).mover state = mover state :=
  rfl
