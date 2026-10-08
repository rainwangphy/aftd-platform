import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExtractTerminalGameTree

/-!
# ExtensiveGame.extractTerminal_payoff

Topic: equilibria   Node: a64e2f03a24a

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.extractTerminal_payoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ExtensiveGame.extractTerminal_payoff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
theorem ExtensiveGame.extractTerminal_payoff (s : G.State) (hs : G.isTerminal s) :
    G.extractTerminalGameTree s hs = GameTree.Leaf (G.payoff s) :=
  rfl
