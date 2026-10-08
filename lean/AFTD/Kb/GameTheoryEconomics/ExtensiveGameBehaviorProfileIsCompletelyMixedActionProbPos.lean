import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileActionProb
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileProbAt
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorProfile.IsCompletelyMixed.actionProb_pos

Topic: equilibria   Node: c1462f401785

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.IsCompletelyMixed.actionProb_pos`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At player-controlled states, a completely mixed behavior profile gives positive probability to every available action.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- At player-controlled states, a completely mixed behavior profile gives positive probability to every available action. -/
theorem ExtensiveGame.BehaviorProfile.IsCompletelyMixed.actionProb_pos {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {beta : G.BehaviorProfile}
    (hbeta : IsCompletelyMixed beta) {s : G.State} {i : iota}
    (hm : G.mover s = some i) (a : G.Action s) :
    0 < beta.actionProb s a := by
  unfold actionProb
  split
  · rename_i j hs
    exact hbeta j s hs (fun hterminal => hterminal.false a) a
  · rename_i hs
    rw [hm] at hs
    cases hs
