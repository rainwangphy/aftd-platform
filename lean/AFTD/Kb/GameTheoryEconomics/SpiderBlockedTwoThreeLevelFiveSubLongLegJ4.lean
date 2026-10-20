import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeReversal
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubLongLegJ4Inward
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_long_leg_j4

Topic: combinatorial_games   Node: c5c5b181aa40

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

Cutting the (5,inward) leg at j = 5 leaves, besides the free legs 2 and 3, a leg of length 4; at fuel 10 the value is 5 both when that leg's far end is inward and when it is outward.
-/

/-- Value 5 of the j = 5 cut of the long leg, for both far ends, at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_long_leg_j4 :
    spider_gamma 10 CentreStatus.none [(4, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 5 ∧
    spider_gamma 10 CentreStatus.none [(4, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 5 :=
  ⟨spider_blocked_two_three_level_five_sub_long_leg_j4_inward,
   (spider_blocked_two_three_reversal 10 4).trans spider_blocked_two_three_level_five_sub_long_leg_j4_inward⟩
