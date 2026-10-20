import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveOptions
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubIncomingTwoThree
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubSumSix
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubSumSeven
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubSumEight
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubSumNine
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubShortLegs
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubLongLegJ34
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubLongLegJ4
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.SpiderGamma

/-!
# spider_blocked_two_three_level_five

Topic: combinatorial_games   Node: 1ad77386e4b3

Provenance: helper lemma. step towards spider_eventual_parity_two_three_blocked_small

At level t = 5, the inward blocked family for the configuration (none; {2^*, 3^*}) at canonical fuel 11 is at most 7.
-/

/-- At level t = 5, the inward blocked family for the configuration (none; {2^*, 3^*}) at canonical fuel 11 is at most 7. -/
theorem spider_blocked_two_three_level_five :
    spider_gamma 11 CentreStatus.none [(5, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] ≤ 7 := by
  rw [spider_blocked_two_three_level_five_options 10,
    spider_blocked_two_three_level_five_sub_incoming_two_three.1,
    spider_blocked_two_three_level_five_sub_incoming_two_three.2,
    spider_blocked_two_three_level_five_sub_sum_six.1,
    spider_blocked_two_three_level_five_sub_sum_six.2,
    spider_blocked_two_three_level_five_sub_sum_seven.1,
    spider_blocked_two_three_level_five_sub_sum_seven.2,
    spider_blocked_two_three_level_five_sub_sum_eight.1,
    spider_blocked_two_three_level_five_sub_sum_eight.2.1,
    spider_blocked_two_three_level_five_sub_long_leg_j4.1,
    spider_blocked_two_three_level_five_sub_sum_nine.1,
    spider_blocked_two_three_level_five_sub_sum_nine.2.1,
    spider_blocked_two_three_level_five_sub_sum_nine.2.2.1,
    spider_blocked_two_three_level_five_sub_sum_nine.2.2.2,
    spider_blocked_two_three_level_five_sub_short_legs.1,
    spider_blocked_two_three_level_five_sub_short_legs.2,
    spider_blocked_two_three_level_five_sub_sum_eight.2.2.1,
    spider_blocked_two_three_level_five_sub_sum_eight.2.2.2,
    spider_blocked_two_three_level_five_sub_long_leg_j34.1,
    spider_blocked_two_three_level_five_sub_long_leg_j34.2]
  decide
