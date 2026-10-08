import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# ExtensiveGame.extractTerminalGameTree

Topic: equilibria   Node: 726931200c24

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.extractTerminalGameTree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Terminal states extract to one-leaf `GameTree`s.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- Terminal states extract to one-leaf `GameTree`s. -/
def ExtensiveGame.extractTerminalGameTree (s : G.State) (_hs : G.isTerminal s) : GameTree N U :=
  GameTree.Leaf (G.payoff s)
