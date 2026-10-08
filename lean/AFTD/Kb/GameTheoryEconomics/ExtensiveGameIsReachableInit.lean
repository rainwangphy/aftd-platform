import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsReachable
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsReachableInit

/-!
# ExtensiveGame.isReachable_init

Topic: equilibria   Node: cd2102b8d05c

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.isReachable_init`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Execution/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The initial state is always reachable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- The initial state is always reachable. -/
theorem ExtensiveGame.isReachable_init (G : ExtensiveGame N U) : G.IsReachable G.init :=
  ControlledGame.isReachable_init G.toControlledGame
