import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsTerminal

/-!
# ControlledGame.NoChance

Topic: equilibria   Node: 21c00cb0b39a

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.NoChance`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every nonterminal state has a strategic mover.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- Every nonterminal state has a strategic mover. -/
def ControlledGame.NoChance (G : ControlledGame N) : Prop :=
  ∀ s : G.State, ¬ G.isTerminal s → ∃ i : N, G.mover s = some i
