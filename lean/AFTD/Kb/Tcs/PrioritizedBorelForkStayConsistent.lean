import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock

/-!
# prioritized_borel_fork_stay_consistent

Topic: automata   Node: d73c019a969b

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

A stay block is consistent with every p-owned choice function.
-/

theorem prioritized_borel_fork_stay_consistent (choice : List PrioritizedBorelForkEdge → Bool)
    (pre : List PrioritizedBorelForkEdge) (b : Bool) :
    prioritized_borel_fork_consistent choice pre (prioritized_borel_fork_three_step_block b false) := by
  cases b <;> simp [prioritized_borel_fork_three_step_block, prioritized_borel_fork_consistent]
