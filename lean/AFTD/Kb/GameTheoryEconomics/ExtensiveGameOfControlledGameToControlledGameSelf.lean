import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGamePayoff

/-!
# ExtensiveGame.ofControlledGame_toControlledGame_self

Topic: equilibria   Node: 564bd41a9a9b

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ofControlledGame_toControlledGame_self`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Forgetting an existing payoff-aware game and then reattaching its payoff recovers the original game definitionally.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- Forgetting an existing payoff-aware game and then reattaching its payoff recovers the original game definitionally. -/
@[simp]
theorem ExtensiveGame.ofControlledGame_toControlledGame_self
    (G : ExtensiveGame N U) :
    ofControlledGame G.toControlledGame G.payoff = G := by
  cases G
  rfl
