import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_blocked_two_three_level_five_sub_long_leg_j34_outward

Topic: combinatorial_games   Node: 5ac4d23f6804

Provenance: helper lemma. step towards spider_blocked_two_three_level_five_sub_long_leg_j34

With free centre, the state whose legs are a length-2 leg with far end outward, the (5,inward) leg, and the free leg 2 has Grundy value 1 at fuel 10.
-/

/-- Value 1 at fuel 10 for the state (none; {(2,outward), (5,inward), 2^*}). -/
theorem spider_blocked_two_three_level_five_sub_long_leg_j34_outward :
    spider_gamma 10 CentreStatus.none [(2, SpiderLegEnd.outward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 1 := by
  decide
