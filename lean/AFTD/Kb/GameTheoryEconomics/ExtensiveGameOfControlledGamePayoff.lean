import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGame

/-!
# ExtensiveGame.ofControlledGame_payoff

Topic: equilibria   Node: dd127d461b38

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ofControlledGame_payoff`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.ofControlledGame_payoff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
@[simp]
theorem ExtensiveGame.ofControlledGame_payoff
    (base : ControlledGame N)
    (payoff : base.State → N → U)
    (state : base.State) (i : N) :
    (ofControlledGame base payoff).payoff state i = payoff state i :=
  rfl
