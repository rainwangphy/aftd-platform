import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentUtility
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.SumRangeGetDAppend

/-!
# proportional_share_utility_eq

Topic: mechanism_design   Node: 954b2ecefeec

In a proportional-share mechanism an agent's utility is s / (s + R) times (pool(s + R) - c).
-/

lemma proportional_share_utility_eq (pool : ℝ → ℝ) (c : ℝ) (mine others : List ℝ) :
    procurement_agent_utility proportional_share_alloc (proportional_share_pay pool) c mine
        others =
      mine.sum / (mine.sum + others.sum) * (pool (mine.sum + others.sum) - c) := by
  unfold procurement_agent_utility proportional_share_pay proportional_share_alloc
  have : ∀ j, (mine ++ others).getD j 0 / (mine ++ others).sum * pool (mine ++ others).sum -
      c * ((mine ++ others).getD j 0 / (mine ++ others).sum) =
      (mine ++ others).getD j 0 * ((pool (mine ++ others).sum - c) / (mine ++ others).sum) := by
    intro j; ring
  simp_rw [this]
  rw [← Finset.sum_mul, sum_range_getD_append, List.sum_append]
  ring
