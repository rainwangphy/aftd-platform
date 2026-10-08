import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaIsTerminal

/-!
# ControlledGame.isNonPlayerState

Topic: equilibria   Node: 589eaf11a36b

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.isNonPlayerState`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonterminal state carrying the non-player-control label. This predicate deliberately supplies no probability law.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- A nonterminal state carrying the non-player-control label. This predicate deliberately supplies no probability law. -/
def ControlledGame.isNonPlayerState (G : ControlledGame N) (s : G.State) : Prop :=
  G.mover s = none ∧ ¬ G.toArena.IsTerminal s
