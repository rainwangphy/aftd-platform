import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsGuaranteedRoundRobinEf1Factor
import AFTD.Kb.GameTheoryEconomics.RoundRobinThreeAgentsPneNotAlphaEf1OfThreeQuartersLt
import AFTD.Kb.GameTheoryEconomics.NotIsGuaranteedRoundRobinEf1FactorThreeOfThreeQuartersLt

/-!
# not_is_guaranteed_round_robin_ef1_factor_three_fifteen_sixteenths

Topic: fair_division   Node: 0327d09afd76

Provenance: helper lemma. arXiv:2610.23686, Prop. 1 and Sec. 6

15/16 is not a guaranteed EF1 factor for Round-Robin pure Nash equilibria with three agents: there exists an 8-good additive instance whose pure Nash equilibrium outcome is not (15/16)-EF1.
-/

/-- 15/16 is not a guaranteed EF1 factor for Round-Robin pure Nash equilibria with three agents. -/
theorem not_is_guaranteed_round_robin_ef1_factor_three_fifteen_sixteenths :
    ¬ is_guaranteed_round_robin_ef1_factor 3 (15 / 16) := by
  apply not_is_guaranteed_round_robin_ef1_factor_three_of_three_quarters_lt
  norm_num
