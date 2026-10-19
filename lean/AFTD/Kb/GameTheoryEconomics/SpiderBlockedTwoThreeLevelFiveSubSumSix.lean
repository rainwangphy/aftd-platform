import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_sum_six

Topic: combinatorial_games   Node: e6f2e0c40799

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

The two sub-states with free centre, a short leg of length 1 whose far end is inward (resp. outward), and the free legs 2 and 3, have value 2 at fuel 10.
-/

/-- Value 2 of the two j = 2 cuts of the long leg, at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_sum_six :
    spider_gamma 10 CentreStatus.none [(1, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 2 ∧
    spider_gamma 10 CentreStatus.none [(1, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 2 := by
  refine ⟨?_, ?_⟩ <;> rw [spider_gamma_fuel_independent 10 _ _ (by decide)] <;> decide
