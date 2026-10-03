import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CostOfEf1
import AFTD.Kb.GameTheoryEconomics.Ef1CostGapInstance
import AFTD.Kb.GameTheoryEconomics.Ef1CostGapInstanceSpec
import AFTD.Kb.GameTheoryEconomics.Ef1GapSetTwoAgentsLe

/-!
# cost_of_ef1_two_le

Topic: fair_division   Node: 954507ee853e

The cost of EF1 for two agents is at most 3 - 2 sqrt 2.
-/

/-- **The cost of EF1 for two agents is at most `3 - 2√2`.** -/
theorem cost_of_ef1_two_le : cost_of_ef1 2 ≤ 3 - 2 * Real.sqrt 2 := by
  refine csSup_le ⟨1 / 6 - 1 / 12, 3, ef1_cost_gap_instance (1 / 12), ?_, ?_⟩
    ef1_gap_set_two_agents_le
  · exact (ef1_cost_gap_instance_spec (1 / 12) (by norm_num) (by norm_num)).1
  · rw [(ef1_cost_gap_instance_spec (1 / 12) (by norm_num) (by norm_num)).2.2.2]
