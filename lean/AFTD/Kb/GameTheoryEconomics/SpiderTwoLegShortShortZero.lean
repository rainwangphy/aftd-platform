import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_two_leg_short_short_zero

Topic: combinatorial_games   Node: 4da1adc810fe

Provenance: helper lemma. step towards spider_blocked_none_one_inward_one_outward

At any fuel at least 3, the two-leg state with centre incoming and legs (1,inward),(1,outward) has value 0, and likewise with centre outgoing.
-/

/-- The two-short-leg sub-state reached by a j = 1 cut of the long leg has value 0 at either centre status. -/
theorem spider_two_leg_short_short_zero (fuel : ℕ) (hfuel : 3 ≤ fuel) :
    spider_gamma fuel CentreStatus.incoming [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)] = 0 ∧
      spider_gamma fuel CentreStatus.outgoing [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)] = 0 := by
  have h : ((List.map Prod.fst [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.outward)]).sum + 1) ≤ fuel := by
    simpa using hfuel
  constructor
  · rw [spider_gamma_fuel_independent fuel _ _ h]
    decide
  · rw [spider_gamma_fuel_independent fuel _ _ h]
    decide
