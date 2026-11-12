import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkRun
import AFTD.Kb.Tcs.PrioritizedBorelForkBlockRun
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkRunAppend
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock

/-!
# prioritized_borel_fork_expand_run

Topic: automata   Node: 72c69d35812d

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Every expanded sequence of paired blocks is a legal run from q back to q.
-/

theorem prioritized_borel_fork_expand_run (u h : List Bool) :
    PrioritizedBorelForkRun 0 (prioritized_borel_fork_expand u h) 0 := by
  induction u generalizing h with
  | nil => simp [prioritized_borel_fork_expand, PrioritizedBorelForkRun.nil]
  | cons b u ih =>
      cases h with
      | nil => simp [prioritized_borel_fork_expand, PrioritizedBorelForkRun.nil]
      | cons c h =>
          simp only [prioritized_borel_fork_expand]
          exact prioritized_borel_fork_run_append (prioritized_borel_fork_block_run b c) (ih h)
