import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_short_legs

Topic: combinatorial_games   Node: f58199789218

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

With centre incoming (resp. outgoing) and the legs (5,inward) and the free leg 2, the value at fuel 10 is 0 (resp. 1).
-/

/-- Values 0 and 1 of the two j = 1 cuts of the free leg 2, at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_short_legs :
    spider_gamma 10 CentreStatus.incoming [(5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 0 ∧
    spider_gamma 10 CentreStatus.outgoing [(5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 1 := by
  refine ⟨?_, ?_⟩ <;> rw [spider_gamma_fuel_independent 10 _ _ (by decide)] <;> decide
