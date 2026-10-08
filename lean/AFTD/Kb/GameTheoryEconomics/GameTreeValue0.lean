import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.value₀

Topic: equilibria   Node: 06be7ae2c446

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Minimax value** for player 0 in a two-player zero-sum game. Under zero-sum, this fully determines both players' values (player 1's value = `-value₀`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- **Minimax value** for player 0 in a two-player zero-sum game. Under zero-sum, this fully determines both players' values (player 1's value = `-value₀`). -/
def GameTree.value₀ (g : GameTree (Fin 2) ℚ) : ℚ :=
  (value g) 0
