import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ArenaFinalState

/-!
# ExtensiveGame.finalState

Topic: equilibria   Node: 05ba7018b454

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.finalState`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Play.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The final state reached from `init` after at most `fuel` steps.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} (G : ExtensiveGame N U) in
/-- The final state reached from `init` after at most `fuel` steps. -/
def ExtensiveGame.finalState (choose : (s : G.State) → G.Action s) (fuel : ℕ) : G.State :=
  G.toArena.finalState choose G.init fuel
