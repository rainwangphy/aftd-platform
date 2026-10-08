import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsPlayerState
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsPlayerState

/-!
# ExtensiveGame.isPlayerState_iff_toControlledGame

Topic: equilibria   Node: 737f6790573e

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.isPlayerState_iff_toControlledGame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The historical payoff-aware player-state predicate is exactly the canonical controlled-game predicate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- The historical payoff-aware player-state predicate is exactly the canonical controlled-game predicate. -/
@[simp]
theorem ExtensiveGame.isPlayerState_iff_toControlledGame
    (G : ExtensiveGame N U) (s : G.State) (i : N) :
    G.isPlayerState s i ↔ G.toControlledGame.isPlayerState s i :=
  Iff.rfl
