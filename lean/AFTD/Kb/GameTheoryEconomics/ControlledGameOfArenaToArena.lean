import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArena

/-!
# ControlledGame.ofArena_toArena

Topic: equilibria   Node: 266e10df93e8

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.ofArena_toArena`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ControlledGame.ofArena_toArena
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
@[simp]
theorem ControlledGame.ofArena_toArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    (ofArena arena init mover).toArena = arena :=
  rfl
