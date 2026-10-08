import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0EqOptStrategyOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeValueOneEqNegValue0
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.value₀_eq_outcome_and_zeroSum

Topic: equilibria   Node: 2fe2c0578aa0

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀_eq_outcome_and_zeroSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Packaging lemma: the backward-induction strategy realizes player 0's value, and the value vector is zero-sum. This is *not* the minimax statement — it has no quantification over opponent strategies. The genuine saddle / security statement is `zermelo_determinacy`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Packaging lemma: the backward-induction strategy realizes player 0's value, and the value vector is zero-sum. This is *not* the minimax statement — it has no quantification over opponent strategies. The genuine saddle / security statement is `zermelo_determinacy`. -/
theorem GameTree.value₀_eq_outcome_and_zeroSum (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    value₀ g = outcome (optStrategy : Strategy (Fin 2) ℚ) g 0 ∧
      (value g) 1 = -value₀ g :=
  ⟨value₀_eq_optStrategy_outcome g, value_one_eq_neg_value₀ g hzs⟩
