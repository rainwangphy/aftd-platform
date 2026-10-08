import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExpectedPayoffFrom
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.expectedPayoff

Topic: equilibria   Node: 0761accb4895

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.expectedPayoff`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite-fuel expected payoff from the initial state under a behavior profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Finite-fuel expected payoff from the initial state under a behavior profile. -/
noncomputable def ExtensiveGame.expectedPayoff (G : ExtensiveGame iota Real)
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    (beta : G.BehaviorProfile) (fuel : Nat) (who : iota) : Real :=
  expectedPayoffFrom beta G.init fuel who
