import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.Tcs.G

/-!
# GameTree.outcome_optStrategy_zero_sum

Topic: equilibria   Node: f2f8c4ddd16f

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.outcome_optStrategy_zero_sum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The terminal outcome reached by the backward-induction strategy is zero-sum whenever the game tree is zero-sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The terminal outcome reached by the backward-induction strategy is zero-sum whenever the game tree is zero-sum. -/
theorem GameTree.outcome_optStrategy_zero_sum (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    outcome (optStrategy : Strategy (Fin 2) ℚ) g 0 +
      outcome (optStrategy : Strategy (Fin 2) ℚ) g 1 = 0 :=
  outcome_zero_sum optStrategy g hzs
