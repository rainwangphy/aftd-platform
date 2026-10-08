import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# ControlledGame.arena

Topic: equilibria   Node: 45d0f79528ed

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.arena`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The arena of a payoff-free controlled game.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- The arena of a payoff-free controlled game. -/
abbrev ControlledGame.arena (G : ControlledGame N) : Arena := G.toArena
