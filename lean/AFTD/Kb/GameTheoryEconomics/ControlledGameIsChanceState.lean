import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsNonPlayerState

/-!
# ControlledGame.isChanceState

Topic: equilibria   Node: a91349048809

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.isChanceState`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Compatibility name for a non-player-controlled nonterminal state. This structural predicate does not assert that a chance law exists. Stochastic layers may interpret such a state as chance only after supplying the relevant law.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- Compatibility name for a non-player-controlled nonterminal state. This structural predicate does not assert that a chance law exists. Stochastic layers may interpret such a state as chance only after supplying the relevant law. -/
abbrev ControlledGame.isChanceState (G : ControlledGame N) (s : G.State) : Prop :=
  G.isNonPlayerState s
