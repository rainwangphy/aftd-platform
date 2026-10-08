import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategyIsSubgamePerfect
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeOptStrategyEqValue
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.Tcs.G

/-!
# GameTree.outcome_le_value₀_of_iVariant_zero

Topic: equilibria   Node: 56ee85624b55

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.outcome_le_value₀_of_iVariant_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Player 1's security.** If player 1 plays `optStrategy` (so `σ'` is a `0`-variant, leaving player 1's choices fixed), then player 0's payoff is at most `value₀ g` against *every* play of player 0. Immediate from subgame perfection at player 0; no zero-sum hypothesis is needed for this direction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- **Player 1's security.** If player 1 plays `optStrategy` (so `σ'` is a `0`-variant, leaving player 1's choices fixed), then player 0's payoff is at most `value₀ g` against *every* play of player 0. Immediate from subgame perfection at player 0; no zero-sum hypothesis is needed for this direction. -/
theorem GameTree.outcome_le_value₀_of_iVariant_zero (g : GameTree (Fin 2) ℚ)
    {σ' : Strategy (Fin 2) ℚ} (hiv : IVariant (0 : Fin 2) optStrategy σ') :
    outcome σ' g 0 ≤ value₀ g := by
  have h0 := optStrategy_isSubgamePerfect g (0 : Fin 2) σ' hiv
  rw [outcome_optStrategy_eq_value] at h0
  simpa [value₀] using h0
