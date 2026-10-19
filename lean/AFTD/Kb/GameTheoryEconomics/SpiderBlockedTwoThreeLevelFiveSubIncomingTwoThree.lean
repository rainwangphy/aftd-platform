import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_incoming_two_three

Topic: combinatorial_games   Node: c2d3278072d5

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

With centre incoming (resp. outgoing) and free legs of length 2 and 3, the value at fuel 10 is 3 (both).
-/

/-- Value 3 of the centre-incoming and centre-outgoing two-legged sub-states at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_incoming_two_three :
    spider_gamma 10 CentreStatus.incoming [(2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 3 ∧
    spider_gamma 10 CentreStatus.outgoing [(2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 3 := by
  refine ⟨?_, ?_⟩ <;> rw [spider_gamma_fuel_independent 10 _ _ (by decide)] <;> decide
