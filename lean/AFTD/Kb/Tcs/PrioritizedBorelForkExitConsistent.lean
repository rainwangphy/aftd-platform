import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkSetup
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock

/-!
# prioritized_borel_fork_exit_consistent

Topic: automata   Node: f88aaf863c1c

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

An excursion block is consistent when its last direction is the function's choice after the first two edges.
-/

theorem prioritized_borel_fork_exit_consistent (choice : List PrioritizedBorelForkEdge → Bool)
    (pre : List PrioritizedBorelForkEdge) :
    prioritized_borel_fork_consistent choice pre
      (prioritized_borel_fork_three_step_block (choice (pre ++ prioritized_borel_fork_setup)) true) := by
  simp [prioritized_borel_fork_three_step_block, prioritized_borel_fork_consistent, prioritized_borel_fork_setup, List.append_assoc]
