import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsReachable
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsReachable

/-!
# ExtensiveGame.isReachable_iff_toControlledGame

Topic: equilibria   Node: a24765a8d346

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.isReachable_iff_toControlledGame`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Execution/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The historical payoff-aware reachability predicate is exactly the canonical controlled-game predicate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- The historical payoff-aware reachability predicate is exactly the canonical controlled-game predicate. -/
@[simp]
theorem ExtensiveGame.isReachable_iff_toControlledGame
    (G : ExtensiveGame N U) (s : G.State) :
    G.IsReachable s ↔ G.toControlledGame.IsReachable s :=
  Iff.rfl
