import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_long_leg_j4_inward

Topic: combinatorial_games   Node: b67ba756ad6a

Provenance: helper lemma. step towards spider_blocked_two_three_level_five_sub_long_leg_j4

With free centre, the state whose legs are the (4,inward) leg together with the free legs 2 and 3 has Grundy value 5 at fuel 10.
-/

/-- The single expensive conjunct of the j = 5 cut of the level-5 long leg: value 5 for the inward continuation. -/
theorem spider_blocked_two_three_level_five_sub_long_leg_j4_inward :
    spider_gamma 10 CentreStatus.none [(4, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 5 := by
  decide
