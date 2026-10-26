import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEF1
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1OfCardLeTwoMul
import AFTD.Kb.GameTheoryEconomics.RoundRobinThreeAgentsSevenGoodsPneEf1
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEnvyZeroEf1OfTwoMulAddOne
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequenceCountLeTwoOfNeZero
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1PairOfCountLeTwo
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation

/-!
# round_robin_pne_ef1_of_card_le_two_mul_add_one

Topic: fair_division   Node: d7ddd1cbd9c1

Provenance: original. Related work: Posed from arXiv:2610.23686 (Proposition 1 and the two-agent theorem); the threshold 2n + 2 is new.

Conjecture: with n agents and at most 2n + 1 goods, every pure Nash equilibrium of Round-Robin (nonnegative additive valuations) is EF1. With round_robin_pne_not_ef1_of_two_mul_add_two this says the least number of goods for which a Round-Robin equilibrium can fail EF1 is exactly 2n + 2 for every n ≥ 3.
-/

theorem round_robin_pne_ef1_of_card_le_two_mul_add_one (n m : ℕ) [NeZero n] (hm : m ≤ 2 * n + 1)
    (w : Fin n → Fin m → ℝ) (hw : ∀ i g, 0 ≤ w i g) (rank : Fin n → Fin m ≃ Fin m)
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence n m) rank) :
    SocialChoice.FairDivision.Indivisible.IsEF1
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (picking_sequence_outcome (round_robin_sequence n m) rank) := by
  by_cases hm0 : m ≤ 2*n
  · exact round_robin_pne_ef1_of_card_le_two_mul n m hm0 w hw rank h
  have hme : m = 2*n+1 := by omega
  subst m
  intro i j hij hnonempty
  by_cases hj : j = 0
  · subst j
    exact round_robin_pne_envy_zero_ef1_of_two_mul_add_one n w hw rank h i hij
  · exact round_robin_pne_ef1_pair_of_count_le_two n (2*n+1) w hw rank h i j hij
      (round_robin_sequence_count_le_two_of_ne_zero n j hj) hnonempty
