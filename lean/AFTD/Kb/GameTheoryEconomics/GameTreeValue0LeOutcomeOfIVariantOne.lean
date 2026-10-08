import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategyIsSubgamePerfect
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeOptStrategyEqValue
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeValueOneEqNegValue0
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.value₀_le_outcome_of_iVariant_one

Topic: equilibria   Node: 85f4982b3399

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀_le_outcome_of_iVariant_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Player 0's security.** If player 0 plays `optStrategy` (so the deviating profile `σ'` is a `1`-variant, leaving player 0's choices fixed), then player 0's payoff is at least `value₀ g` against *every* play of player 1. Proof: subgame perfection at player 1 caps `outcome σ' g 1 ≤ value g 1 = -value₀ g`; the zero-sum identity `outcome σ' g 0 = -outcome σ' g 1` then forces `outcome σ' g 0 ≥ value₀ g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- **Player 0's security.** If player 0 plays `optStrategy` (so the deviating profile `σ'` is a `1`-variant, leaving player 0's choices fixed), then player 0's payoff is at least `value₀ g` against *every* play of player 1. Proof: subgame perfection at player 1 caps `outcome σ' g 1 ≤ value g 1 = -value₀ g`; the zero-sum identity `outcome σ' g 0 = -outcome σ' g 1` then forces `outcome σ' g 0 ≥ value₀ g`. -/
theorem GameTree.value₀_le_outcome_of_iVariant_one (g : GameTree (Fin 2) ℚ)
    (hzs : IsZeroSum g) {σ' : Strategy (Fin 2) ℚ}
    (hiv : IVariant (1 : Fin 2) optStrategy σ') :
    value₀ g ≤ outcome σ' g 0 := by
  have h1 := optStrategy_isSubgamePerfect g (1 : Fin 2) σ' hiv
  rw [outcome_optStrategy_eq_value, value_one_eq_neg_value₀ g hzs] at h1
  have hsum := outcome_zero_sum σ' g hzs
  linarith
