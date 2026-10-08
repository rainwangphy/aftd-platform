import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileActionProb
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame

/-!
# ExtensiveGame.BehaviorProfile.actionProb_nonneg

Topic: equilibria   Node: 80f1d0f3d05f

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.actionProb_nonneg`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A behavior profile assigns nonnegative probability to every action.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- A behavior profile assigns nonnegative probability to every action. -/
theorem ExtensiveGame.BehaviorProfile.actionProb_nonneg {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (s : G.State) (a : G.Action s) :
    0 <= beta.actionProb s a := by
  unfold actionProb
  split
  · rename_i i hm
    exact
      (beta i s hm
        (fun hterminal => hterminal.false a)).property.1 a
  · norm_num
