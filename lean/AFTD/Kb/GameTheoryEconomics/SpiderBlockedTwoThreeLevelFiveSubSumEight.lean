import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_sum_eight

Topic: combinatorial_games   Node: c7699eaba52d

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

Four sub-states at fuel 10: the two states obtained by cutting the long leg at j = 4, which add a leg of length 3 with far end inward (resp. outward) to the free legs 2 and 3, have value 7; and the two states obtained by cutting the free leg of length 3 at j = 2, which add a leg of length 1 with far end inward (resp. outward) to (5,inward) and (2,free), have value 1 (inward) and 0 (outward).
-/

/-- Values 7, 7, 1, 0 of the j = 4 long-leg cuts and the j = 2 cuts of the free leg 3, at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_sum_eight :
    spider_gamma 10 CentreStatus.none [(3, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 7 ∧
    spider_gamma 10 CentreStatus.none [(3, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 7 ∧
    spider_gamma 10 CentreStatus.none [(1, SpiderLegEnd.inward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 1 ∧
    spider_gamma 10 CentreStatus.none [(1, SpiderLegEnd.outward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [spider_gamma_fuel_independent 10 _ _ (by decide)] <;> decide
