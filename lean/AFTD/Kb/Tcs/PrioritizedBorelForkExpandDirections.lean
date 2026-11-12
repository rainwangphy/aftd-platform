import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock

/-!
# prioritized_borel_fork_expand_directions

Topic: automata   Node: 0ada3564f293

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Expanding equally long block histories has directions false, false, then the visible bit in each block.
-/

theorem prioritized_borel_fork_expand_directions (u h : List Bool) (hlen : u.length = h.length) :
    (prioritized_borel_fork_expand u h).map PrioritizedBorelForkEdge.dir =
      u.flatMap (fun b => [false, false, b]) := by
  induction u generalizing h with
  | nil => cases h <;> simp_all [prioritized_borel_fork_expand]
  | cons b u ih =>
      cases h with
      | nil => simp at hlen
      | cons c h =>
          have hh : u.length = h.length := by simpa using hlen
          cases c <;> simp [prioritized_borel_fork_expand, prioritized_borel_fork_three_step_block, ih h hh]
