import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MmsThresholdMonotone
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotoneOfLe
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotoneTwoThree
import AFTD.Kb.GameTheoryEconomics.MmsTwoAgentsFourGoodsNotExists

/-!
# mms_threshold_monotone_two

Topic: fair_division   Node: d307a835fe2d

Provenance: original. Related work: exact value of the threshold μ(n) of arXiv:2610.06125 (On MMS allocations with few items) at n = 2 (the paper studies the asymptotics; for additive valuations μ(2) is unbounded by cut and choose)

μ(2) = 3 for monotone valuations over goods: every instance with two agents and at most three goods has an MMS allocation, and some instance with four goods has none.
-/

theorem mms_threshold_monotone_two : mms_threshold_monotone 2 = 3 := by
  apply IsGreatest.csSup_eq
  refine ⟨fun m' hm' => ?_, fun m hm => ?_⟩
  · rcases Nat.lt_or_ge m' 3 with h | h
    · exact mms_exists_monotone_of_le 2 m' (by norm_num) (by omega)
    · obtain rfl : m' = 3 := by omega
      exact mms_exists_monotone_two_three
  · by_contra h
    exact mms_two_agents_four_goods_not_exists (hm 4 (by omega))
