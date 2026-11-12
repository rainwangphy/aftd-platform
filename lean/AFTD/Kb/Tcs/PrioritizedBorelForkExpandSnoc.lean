import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_expand_snoc

Topic: automata   Node: ae6413bd402e

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Appending a visible bit and hidden decision appends the corresponding three-edge block to the expanded history.
-/

theorem prioritized_borel_fork_expand_snoc (u h : List Bool) (hlen : u.length = h.length)
    (b c : Bool) :
    prioritized_borel_fork_expand (u ++ [b]) (h ++ [c]) =
      prioritized_borel_fork_expand u h ++ prioritized_borel_fork_three_step_block b c := by
  induction u generalizing h with
  | nil => cases h <;> simp_all [prioritized_borel_fork_expand]
  | cons a u ih =>
      cases h with
      | nil => simp at hlen
      | cons x h =>
          have hh : u.length = h.length := by simpa using hlen
          simp [prioritized_borel_fork_expand, ih h hh, List.append_assoc]
