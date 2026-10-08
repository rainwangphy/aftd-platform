import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExtractsGameTree
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExtractTerminalGameTree
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExtractTerminalPayoff

/-!
# ExtensiveGame.extractTerminal_extracts

Topic: equilibria   Node: 9bf73e434008

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.extractTerminal_extracts`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The certified terminal-state extractor satisfies the relational extraction interface.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- The certified terminal-state extractor satisfies the relational extraction interface. -/
theorem ExtensiveGame.extractTerminal_extracts (s : G.State) (hs : G.isTerminal s) :
    ExtractsGameTree G s (G.extractTerminalGameTree s hs) := by
  rw [extractTerminal_payoff]
  exact ExtractsGameTree.leaf s hs
