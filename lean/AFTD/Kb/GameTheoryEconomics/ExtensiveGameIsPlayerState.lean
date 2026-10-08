import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsPlayerState

/-!
# ExtensiveGame.isPlayerState

Topic: equilibria   Node: 427d31519317

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.isPlayerState`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is controlled by player `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- A state is controlled by player `i`. -/
def ExtensiveGame.isPlayerState (G : ExtensiveGame N U) (s : G.State) (i : N) : Prop :=
  G.toControlledGame.isPlayerState s i
