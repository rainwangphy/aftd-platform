import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1PairOfCountLeTwo
import AFTD.Kb.GameTheoryEconomics.RoundRobinTwoMulAddOneDeviationCertificate
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEnvyZeroEf1OfDeviationCertificate
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation

/-!
# round_robin_pne_envy_zero_ef1_of_two_mul_add_one

Topic: fair_division   Node: ed9dda8a725e

Provenance: helper lemma. The remaining case of the conjecture round_robin_pne_ef1_of_card_le_two_mul_add_one (thread RT-3); exact for n = 3 by exp 1515, sampled for n = 4..6 by exp 1598.

With n agents and 2n + 1 goods, in every pure Nash equilibrium of Round-Robin (nonnegative additive valuations) every agent i ≠ 0 is EF1 towards agent 0, the only agent with three goods. With round_robin_pne_ef1_pair_of_count_le_two and round_robin_sequence_count_le_two_of_ne_zero this is the m = 2n + 1 case of round_robin_pne_ef1_of_card_le_two_mul_add_one.
-/

theorem round_robin_pne_envy_zero_ef1_of_two_mul_add_one (n : ℕ) [NeZero n]
    (w : Fin n → Fin (2 * n + 1) → ℝ) (hw : ∀ i g, 0 ≤ w i g)
    (rank : Fin n → Fin (2 * n + 1) ≃ Fin (2 * n + 1))
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence n (2 * n + 1)) rank)
    (i : Fin n) (hi : i ≠ 0) :
    ∃ g ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0,
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val i
          (picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g}) ≤
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val i
          (picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i) := by
  exact round_robin_pne_envy_zero_ef1_of_deviation_certificate n w hw rank h i hi
    (round_robin_two_mul_add_one_deviation_certificate n rank i hi)
