import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaToArena

/-!
# ControlledGame.ofArena_init

Topic: equilibria   Node: 4db24c8bd992

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.ofArena_init`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ControlledGame.ofArena_init
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
@[simp]
theorem ControlledGame.ofArena_init (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    (ofArena arena init mover).init = init :=
  rfl
