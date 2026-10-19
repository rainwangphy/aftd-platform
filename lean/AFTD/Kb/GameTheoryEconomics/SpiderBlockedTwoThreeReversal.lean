import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaReversal
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderReverseLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderReverseCentreStatus

/-!
# spider_blocked_two_three_reversal

Topic: combinatorial_games   Node: 139cb6647e68

Provenance: helper lemma. step towards spider_eventual_parity_two_three_blocked_small

For any fuel and leg length t, the spider gamma value with centre none and legs (t, outward), (2, free), (3, free) equals the gamma value with (t, inward), (2, free), (3, free).
-/

/-- For the spider state with legs (t, delta), (2, free), (3, free) and centre none, outward and inward orientations of the first leg yield equal gamma values for all fuels. -/
theorem spider_blocked_two_three_reversal (fuel t : ℕ) :
    spider_gamma fuel CentreStatus.none [(t, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] =
    spider_gamma fuel CentreStatus.none [(t, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] := by
  rw [spider_gamma_reversal fuel CentreStatus.none
    [(t, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)]]
  rfl
