import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileIsCompletelyMixedWithPositiveReach
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachProb
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach.mixed

Topic: equilibria   Node: 7d790e55a078

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach.mixed`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The complete-mixing component of `IsCompletelyMixedWithPositiveReach`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- The complete-mixing component of `IsCompletelyMixedWithPositiveReach`. -/
theorem ExtensiveGame.BehaviorProfile.IsCompletelyMixedWithPositiveReach.mixed {G : ExtensiveGame iota U}
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    {beta : G.BehaviorProfile} {fuel : Nat}
    (hbeta : IsCompletelyMixedWithPositiveReach beta fuel) :
    IsCompletelyMixed beta :=
  hbeta.1
