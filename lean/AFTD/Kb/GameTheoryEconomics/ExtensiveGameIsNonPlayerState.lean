import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ControlledGameIsNonPlayerState

/-!
# ExtensiveGame.isNonPlayerState

Topic: equilibria   Node: ae9f15e1cdb5

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.isNonPlayerState`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonterminal state carrying the non-player-control label. This predicate supplies no probability law.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- A nonterminal state carrying the non-player-control label. This predicate supplies no probability law. -/
def ExtensiveGame.isNonPlayerState (G : ExtensiveGame N U) (s : G.State) : Prop :=
  G.toControlledGame.isNonPlayerState s
