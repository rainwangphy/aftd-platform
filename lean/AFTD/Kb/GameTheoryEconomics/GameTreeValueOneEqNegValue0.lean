import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.value_one_eq_neg_value₀

Topic: equilibria   Node: dd56fa94cec4

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value_one_eq_neg_value₀`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a zero-sum game, player 1's backward-induction value is determined by player 0's value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- In a zero-sum game, player 1's backward-induction value is determined by player 0's value. -/
theorem GameTree.value_one_eq_neg_value₀ (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (value g) 1 = -value₀ g := by
  unfold value₀
  have h := value_zero_sum g hzs
  linarith
