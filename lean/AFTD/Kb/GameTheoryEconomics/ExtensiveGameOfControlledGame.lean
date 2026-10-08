import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame

/-!
# ExtensiveGame.ofControlledGame

Topic: equilibria   Node: e9402ef6ce93

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ofControlledGame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Add a state-based payoff interpretation to a payoff-free controlled game. Forgetting the result with `ExtensiveGame.toControlledGame` recovers `base` definitionally.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- Add a state-based payoff interpretation to a payoff-free controlled game. Forgetting the result with `ExtensiveGame.toControlledGame` recovers `base` definitionally. -/
abbrev ExtensiveGame.ofControlledGame (base : ControlledGame N)
    (payoff : base.State → N → U) :
    ExtensiveGame N U where
  toControlledGame := base
  payoff := payoff
