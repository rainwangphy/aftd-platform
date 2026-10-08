import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameNoChance

/-!
# ExtensiveGame.NoChance

Topic: equilibria   Node: 210dbff7a2df

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.NoChance`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

No chance nodes: every nonterminal state has a strategic mover.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- No chance nodes: every nonterminal state has a strategic mover. -/
def ExtensiveGame.NoChance (G : ExtensiveGame N U) : Prop :=
  G.toControlledGame.NoChance
