import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubLongLegJ34Inward
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFiveSubLongLegJ34Outward
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_blocked_two_three_level_five_sub_long_leg_j34

Topic: combinatorial_games   Node: 52d47798c294

Provenance: helper lemma. step towards spider_blocked_two_three_level_five

With free centre, the state obtained from (none;{(5,inward),2^*,3^*}) by cutting the (5,inward) leg at j = 4 leaves a leg of length 2 with far end inward (resp. outward) in front of (5,inward) and the free leg 2; the values at fuel 10 are 0 and 1.
-/

/-- Values 0 and 1 of the two j = 3 cuts of the free leg 2, at fuel 10. -/
theorem spider_blocked_two_three_level_five_sub_long_leg_j34 :
    spider_gamma 10 CentreStatus.none [(2, SpiderLegEnd.inward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 0 ∧
    spider_gamma 10 CentreStatus.none [(2, SpiderLegEnd.outward), (5, SpiderLegEnd.inward), (2, SpiderLegEnd.free)] = 1 := ⟨spider_blocked_two_three_level_five_sub_long_leg_j34_inward, spider_blocked_two_three_level_five_sub_long_leg_j34_outward⟩
