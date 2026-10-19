import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_sum_nine

Topic: combinatorial_games   Node: 5a28efba1599

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

Four sub-states at fuel 10: the states (incoming;{(5,inward),(3,free)}) and (outgoing;{(5,inward),(3,free)}) have value 4 and 6, and the states with free centre obtained by cutting the free leg of length 3 at j = 1, which add a leg of length 2 with far end inward (resp. outward) to (5,inward), have value 2 and 3.
-/

/-- Values 4, 6, 2, 3 of the sub-states reached from the free leg 3, at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_sum_nine :
    spider_gamma 10 CentreStatus.incoming [(5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)] = 4 ∧
    spider_gamma 10 CentreStatus.outgoing [(5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)] = 6 ∧
    spider_gamma 10 CentreStatus.none [(1, SpiderLegEnd.inward), (5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)] = 2 ∧
    spider_gamma 10 CentreStatus.none [(1, SpiderLegEnd.outward), (5, SpiderLegEnd.inward), (3, SpiderLegEnd.free)] = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [spider_gamma_fuel_independent 10 _ _ (by decide)] <;> decide
