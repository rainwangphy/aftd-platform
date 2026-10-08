import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# ControlledGame.isPlayerState

Topic: equilibria   Node: d88b4e51dde7

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.isPlayerState`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is controlled by player `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- A state is controlled by player `i`. -/
def ControlledGame.isPlayerState (G : ControlledGame N) (s : G.State) (i : N) : Prop :=
  G.mover s = some i
