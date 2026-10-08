import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorProfile.probAt

Topic: equilibria   Node: 4359788c533a

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.probAt`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The probability that a behavior profile assigns to action `a` at a state controlled by player `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- The probability that a behavior profile assigns to action `a` at a state controlled by player `i`. -/
def ExtensiveGame.BehaviorProfile.probAt {G : ExtensiveGame iota U} [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile)
    {s : G.State} {i : iota} (h : G.mover s = some i) (a : G.Action s) : Real :=
  (beta i s h (fun hterminal => hterminal.false a)).val a
