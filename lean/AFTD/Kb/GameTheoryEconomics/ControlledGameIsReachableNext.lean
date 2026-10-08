import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsReachable
import AFTD.Kb.GameTheoryEconomics.ArenaReachableStep'

/-!
# ControlledGame.IsReachable.next

Topic: equilibria   Node: 27c9ffa63206

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.IsReachable.next`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A legal successor of a reachable state is reachable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- A legal successor of a reachable state is reachable. -/
theorem ControlledGame.IsReachable.next {G : ControlledGame N} {state : G.State}
    (h : G.IsReachable state) (action : G.Action state) :
    G.IsReachable (G.next state action) :=
  h.step' action
