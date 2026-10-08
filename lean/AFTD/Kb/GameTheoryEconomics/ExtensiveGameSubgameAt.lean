import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame

/-!
# ExtensiveGame.subgameAt

Topic: equilibria   Node: 6ae3e9d848cb

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.subgameAt`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Subgame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The subgame starting at state `s`: same arena, different starting point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- The subgame starting at state `s`: same arena, different starting point. -/
def ExtensiveGame.subgameAt (G : ExtensiveGame N U) (s : G.State) : ExtensiveGame N U :=
  { G with init := s }
