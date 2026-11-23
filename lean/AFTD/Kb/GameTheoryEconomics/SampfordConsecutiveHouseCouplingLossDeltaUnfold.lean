import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordWeight
import AFTD.Kb.GameTheoryEconomics.SampfordTotalWeight
import AFTD.Kb.GameTheoryEconomics.SampfordProbSubset
import AFTD.Kb.GameTheoryEconomics.SampfordIsCoupling
import AFTD.Kb.GameTheoryEconomics.SampfordCouplingLoss
import AFTD.Kb.GameTheoryEconomics.SampfordConsecutiveHouseCouplingLossDelta

/-!
# sampford_consecutive_house_coupling_loss_delta_unfold

Topic: social_choice   Node: 91ac1492c7ff

Provenance: helper lemma. step towards sampford_consecutive_house_coupling_loss_delta_four

Delta_n is the supremum, over all positive vote-share vectors p and all house sizes h >= 1, of the infimum over all valid couplings of the coupling loss, where validity and loss are given by the reified definitions sampfordIsCoupling and sampfordCouplingLoss.
-/

/-- Definitional unfolding of Delta_n in terms of the reified Sampford machinery. -/
theorem sampford_consecutive_house_coupling_loss_delta_unfold (n : ℕ) :
    sampfordConsecutiveHouseCouplingLossDelta n =
      sSup { v | ∃ (p : Fin n → ℝ) (h : ℕ),
        (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ 1 ≤ h ∧
        v = sInf { L | ∃ prob, sampfordIsCoupling p h prob ∧ L = sampfordCouplingLoss p h prob } } := by
  simp only [sampfordConsecutiveHouseCouplingLossDelta, sampfordIsCoupling,
    sampfordCouplingLoss, sampfordProbSubset, sampfordTotalWeight, sampfordWeight]
