import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedVal
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_two_leg_blocked_incoming_base

Topic: combinatorial_games   Node: ac301585dade

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

The closed form holds at r = 0 and r = 1: spider_gamma 2 incoming [(0,inward),(1,free)] = 1, spider_gamma 2 incoming [(0,outward),(1,free)] = 1, spider_gamma 3 incoming [(1,inward),(1,free)] = 2 and spider_gamma 3 incoming [(1,outward),(1,free)] = 0, matching spider_blocked_val in each case.
-/

/-- Base cases r = 0 and r = 1 of the blocked two-leg closed form, for both end conditions. -/
theorem spider_two_leg_blocked_incoming_base :
    spider_gamma 2 CentreStatus.incoming [(0, SpiderLegEnd.inward), (1, SpiderLegEnd.free)]
        = spider_blocked_val SpiderLegEnd.inward 0 ∧
    spider_gamma 2 CentreStatus.incoming [(0, SpiderLegEnd.outward), (1, SpiderLegEnd.free)]
        = spider_blocked_val SpiderLegEnd.outward 0 ∧
    spider_gamma 3 CentreStatus.incoming [(1, SpiderLegEnd.inward), (1, SpiderLegEnd.free)]
        = spider_blocked_val SpiderLegEnd.inward 1 ∧
    spider_gamma 3 CentreStatus.incoming [(1, SpiderLegEnd.outward), (1, SpiderLegEnd.free)]
        = spider_blocked_val SpiderLegEnd.outward 1 :=
  ⟨rfl, rfl, rfl, rfl⟩
