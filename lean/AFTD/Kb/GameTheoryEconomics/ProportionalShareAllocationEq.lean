import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentAllocation
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.SumRangeGetDAppend

/-!
# proportional_share_allocation_eq

Topic: mechanism_design   Node: 55b3e1997bc6

In a proportional-share mechanism an agent's total work is s / (s + R), s its total bid and R the others' total.
-/

lemma proportional_share_allocation_eq (mine others : List ℝ) :
    procurement_agent_allocation proportional_share_alloc mine others =
      mine.sum / (mine.sum + others.sum) := by
  unfold procurement_agent_allocation proportional_share_alloc
  rw [← Finset.sum_div, sum_range_getD_append, List.sum_append]
