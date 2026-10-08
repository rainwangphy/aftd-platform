import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameFinalState

/-!
# ExtensiveGame.finalPayoff

Topic: equilibria   Node: 9149c6c6c6dc

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.finalPayoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Play.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Payoff at the final state for player `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} (G : ExtensiveGame N U) in
/-- Payoff at the final state for player `i`. -/
def ExtensiveGame.finalPayoff (choose : (s : G.State) → G.Action s) (fuel : ℕ) (i : N) : U :=
  G.payoff (G.finalState choose fuel) i
