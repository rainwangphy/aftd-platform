import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaReachable

/-!
# ControlledGame.IsReachable

Topic: equilibria   Node: 16cc29c1e707

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.IsReachable`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is reachable in a controlled game if it is reachable from its distinguished initial state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- A state is reachable in a controlled game if it is reachable from its distinguished initial state. -/
def ControlledGame.IsReachable (G : ControlledGame N) (state : G.State) : Prop :=
  G.toArena.Reachable G.init state
