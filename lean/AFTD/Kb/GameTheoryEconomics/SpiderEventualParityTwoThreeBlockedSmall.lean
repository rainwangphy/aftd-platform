import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderGammaFuelIndependent
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeReversal
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFour
import AFTD.Kb.GameTheoryEconomics.SpiderBlockedTwoThreeLevelFive
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderGamma
import AFTD.Kb.GameTheoryEconomics.CentreStatus

/-!
# spider_eventual_parity_two_three_blocked_small

Topic: combinatorial_games   Node: cb77692c4f12

Provenance: helper lemma. step towards spider_eventual_parity_two_three

For the configuration κ0 = (none;{2^*,3^*}), the blocked family at level t is 2 for t = 1 and 6 for t = 2, for both far ends, and it is at most 7 for t = 3, 4, 5.
-/

lemma spider_eventual_parity_two_three_blocked_small_level_one :
    spider_gamma 7 CentreStatus.none [(1, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 2 := by
  decide

lemma spider_eventual_parity_two_three_blocked_small_level_two :
    spider_gamma 8 CentreStatus.none [(2, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 6 := by
  decide

lemma spider_eventual_parity_two_three_blocked_small_level_three :
    spider_gamma 9 CentreStatus.none [(3, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] ≤ 7 := by
  decide

/-- The two small blocked values of the κ0 family: at levels 1 and 2 the blocked families of κ0 = (none;{2^*,3^*}) take the values 2 and 6 (paper Table 6). -/
theorem spider_eventual_parity_two_three_blocked_small :
    spider_gamma 7 CentreStatus.none [(1, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 2 ∧
    spider_gamma 7 CentreStatus.none [(1, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 2 ∧
    spider_gamma 8 CentreStatus.none [(2, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 6 ∧
    spider_gamma 8 CentreStatus.none [(2, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 6 ∧
    (∀ t : ℕ, 3 ≤ t → t ≤ 5 →
      spider_gamma (t + 6) CentreStatus.none [(t, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] ≤ 7) ∧
    (∀ t : ℕ, 3 ≤ t → t ≤ 5 →
      spider_gamma (t + 6) CentreStatus.none [(t, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] ≤ 7) := by
  have h1 : spider_gamma 7 CentreStatus.none [(1, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 2 :=
    spider_eventual_parity_two_three_blocked_small_level_one
  have h1_out : spider_gamma 7 CentreStatus.none [(1, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 2 := by
    rw [spider_blocked_two_three_reversal, h1]
  have h2 : spider_gamma 8 CentreStatus.none [(2, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 6 :=
    spider_eventual_parity_two_three_blocked_small_level_two
  have h2_out : spider_gamma 8 CentreStatus.none [(2, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] = 6 := by
    rw [spider_blocked_two_three_reversal, h2]
  have h_in : ∀ t : ℕ, 3 ≤ t → t ≤ 5 →
      spider_gamma (t + 6) CentreStatus.none [(t, SpiderLegEnd.inward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] ≤ 7 := by
    intro t ht3 ht5
    interval_cases t
    · exact spider_eventual_parity_two_three_blocked_small_level_three
    · exact spider_blocked_two_three_level_four
    · exact spider_blocked_two_three_level_five
  have h_out : ∀ t : ℕ, 3 ≤ t → t ≤ 5 →
      spider_gamma (t + 6) CentreStatus.none [(t, SpiderLegEnd.outward), (2, SpiderLegEnd.free), (3, SpiderLegEnd.free)] ≤ 7 := by
    intro t ht3 ht5
    rw [spider_blocked_two_three_reversal]
    exact h_in t ht3 ht5
  exact ⟨h1, h1_out, h2, h2_out, h_in, h_out⟩
