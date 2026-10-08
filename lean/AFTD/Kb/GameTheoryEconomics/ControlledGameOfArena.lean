import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame

/-!
# ControlledGame.ofArena

Topic: equilibria   Node: 754e8073dd74

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.ofArena`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Add an initial state and mover assignment to an ordinary arena.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- Add an initial state and mover assignment to an ordinary arena. -/
abbrev ControlledGame.ofArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    ControlledGame N where
  toArena := arena
  init := init
  mover := mover
