import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_blocked_two_three_level_five_sub_long_leg_j34_inward

Topic: combinatorial_games   Node: a3c467551277

Provenance: helper lemma. step towards spider_blocked_two_three_level_five_sub_long_leg_j34

With free centre, the state whose legs are a length-2 leg with far end inward, the (5,inward) leg, and the free leg 2 has Grundy value 0 at fuel 10.
-/

/-- Value 0 at fuel 10 for the state (none; {(2,inward), (5,inward), 2^*}). -/
theorem spider_blocked_two_three_level_five_sub_long_leg_j34_inward :
    spider_gamma 10 CentreStatus.none [(2, SpiderLegEnd.inward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 0 := by
  decide
