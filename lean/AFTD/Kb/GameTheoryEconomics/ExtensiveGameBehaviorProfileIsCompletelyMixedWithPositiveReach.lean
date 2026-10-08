import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachProb
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach

Topic: equilibria   Node: d8020eaf6ebd

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Completely mixed behavior together with the current positive-reach interface for every subgame root at a fixed fuel. In finite games with explicit positive chance probabilities, the second component follows from complete mixing and reachability of every game-tree vertex. The Arena behavior layer currently keeps chance probabilities and finite-depth bounds abstract, so Corollary 7.7 uses this as the precise bridge from complete mixing to the positive-reach hypothesis of Theorem 7.5.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Completely mixed behavior together with the current positive-reach interface for every subgame root at a fixed fuel. In finite games with explicit positive chance probabilities, the second component follows from complete mixing and reachability of every game-tree vertex. The Arena behavior layer currently keeps chance probabilities and finite-depth bounds abstract, so Corollary 7.7 uses this as the precise bridge from complete mixing to the positive-reach hypothesis of Theorem 7.5. -/
def ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach {G : ExtensiveGame iota U}
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (fuel : Nat) : Prop :=
  IsCompletelyMixed beta /\ forall root : G.State, 0 < reachProb G beta root fuel
