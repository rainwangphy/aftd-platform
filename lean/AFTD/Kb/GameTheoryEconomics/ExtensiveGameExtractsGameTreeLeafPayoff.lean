import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExtractsGameTree
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameActionListComplete

/-!
# ExtensiveGame.ExtractsGameTree.leaf_payoff

Topic: equilibria   Node: e6a059a7b7f9

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ExtractsGameTree.leaf_payoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If an Arena state extracts to a leaf, the leaf payoff is exactly the Arena payoff at that state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- If an Arena state extracts to a leaf, the leaf payoff is exactly the Arena payoff at that state. -/
theorem ExtensiveGame.ExtractsGameTree.leaf_payoff {s : G.State} {p : N → U}
    (h : ExtractsGameTree G s (GameTree.Leaf p)) :
    p = G.payoff s := by
  cases h
  rfl
