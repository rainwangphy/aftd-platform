import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkRun
import AFTD.Kb.Tcs.PrioritizedBorelForkIsLegal
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_block_run

Topic: automata   Node: 5685b4ff6775

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Each three-edge stay or excursion is a legal run from q back to q.
-/

theorem prioritized_borel_fork_block_run (b c : Bool) : PrioritizedBorelForkRun 0 (prioritized_borel_fork_three_step_block b c) 0 := by
  cases b <;> cases c <;>
    simp only [prioritized_borel_fork_three_step_block, Bool.false_eq_true, ↓reduceIte] <;>
    refine PrioritizedBorelForkRun.cons ?_ rfl (PrioritizedBorelForkRun.cons ?_ rfl
      (PrioritizedBorelForkRun.cons ?_ rfl (PrioritizedBorelForkRun.nil _))) <;>
    norm_num [prioritized_borel_fork_is_legal]
