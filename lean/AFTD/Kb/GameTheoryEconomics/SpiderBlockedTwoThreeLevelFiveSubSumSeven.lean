import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_sum_seven

Topic: combinatorial_games   Node: b3f20134c358

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

The two sub-states with free centre where a leg of length 2 with far end inward (resp. outward) is added to the free legs 2 and 3 have value 6 at fuel 10.
-/

/-- Value 6 of the two j = 3 cuts of the long leg, at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_sum_seven :
    spider_gamma 10 CentreStatus.none [(2, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 6 ∧
    spider_gamma 10 CentreStatus.none [(2, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 6 := by
  refine ⟨?_, ?_⟩ <;> rw [spider_gamma_fuel_independent 10 _ _ (by decide)] <;> decide
