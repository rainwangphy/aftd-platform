import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsReachable

/-!
# ExtensiveGame.IsReachable

Topic: equilibria   Node: d2c73cbd9c7e

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.IsReachable`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Execution/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is reachable in the game if it is reachable from `init`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- A state is reachable in the game if it is reachable from `init`. -/
def ExtensiveGame.IsReachable (G : ExtensiveGame N U) (s : G.State) : Prop :=
  G.toControlledGame.IsReachable s
