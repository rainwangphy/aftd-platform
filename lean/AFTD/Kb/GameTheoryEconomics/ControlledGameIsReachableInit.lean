import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsReachable
import AFTD.Kb.GameTheoryEconomics.ArenaReachable

/-!
# ControlledGame.isReachable_init

Topic: equilibria   Node: 783c1e0784ff

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.isReachable_init`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The initial state is reachable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- The initial state is reachable. -/
theorem ControlledGame.isReachable_init (G : ControlledGame N) : G.IsReachable G.init :=
  .refl _
