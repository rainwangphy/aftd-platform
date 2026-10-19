import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_blocked_two_three_level_four

Topic: combinatorial_games   Node: 07e7baa979c2

Provenance: helper lemma. step towards spider_eventual_parity_two_three_blocked_small

At level t = 4, the inward blocked family for the configuration (none; {2^*, 3^*}) at canonical fuel 10 is at most 7.
-/

/-- At level t = 4, the inward blocked family for the configuration (none; {2^*, 3^*}) at canonical fuel 10 is at most 7. -/
theorem spider_blocked_two_three_level_four :
    spider_gamma 10 CentreStatus.none [(4, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] ≤ 7 := by
  decide
