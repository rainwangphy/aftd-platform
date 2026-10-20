import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsGuaranteedRoundRobinEf1Factor
import AFTD.Kb.GameTheoryEconomics.RoundRobinThreeAgentsPneNotAlphaEf1OfThreeQuartersLt
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# not_is_guaranteed_round_robin_ef1_factor_three_of_three_quarters_lt

Topic: fair_division   Node: a83eacf8fb72

Provenance: helper lemma. arXiv:2610.23686, Sec. 6

For three agents, no factor strictly greater than 3/4 is guaranteed for Round-Robin pure Nash equilibria.
-/

/-- No factor α > 3/4 is guaranteed for Round-Robin pure Nash equilibria with three agents. -/
theorem not_is_guaranteed_round_robin_ef1_factor_three_of_three_quarters_lt (α : ℝ) (hα : 3 / 4 < α) :
    ¬ is_guaranteed_round_robin_ef1_factor 3 α := by
  intro h
  rcases round_robin_three_agents_pne_not_alpha_ef1_of_three_quarters_lt with ⟨w, rank, hw, hpne, hnot⟩
  exact hnot α hα (h 8 w hw rank hpne)
