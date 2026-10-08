import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal

/-!
# ExtensiveGame.Strategy

Topic: equilibria   Node: 32ddb179435f

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.Strategy`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Strategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strategy for player `i`: at each nonterminal state where `i` is the mover, specify which action to take. The nonterminal premise is essential because terminal mover labels are semantically ignored by `ControlledGame`. In particular, a terminal state labelled `some i` does not create an impossible strategy coordinate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- A strategy for player `i`: at each nonterminal state where `i` is the mover, specify which action to take. The nonterminal premise is essential because terminal mover labels are semantically ignored by `ControlledGame`. In particular, a terminal state labelled `some i` does not create an impossible strategy coordinate. -/
def ExtensiveGame.Strategy (G : ExtensiveGame N U) (i : N) :=
  (s : G.State) → G.mover s = some i →
    ¬ G.isTerminal s → G.Action s
