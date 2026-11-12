import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkHiddenDecode
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_decode_expand

Topic: automata   Node: 5fa73a475e27

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Expanding equally long visible and hidden block histories and decoding the result recovers the hidden history.
-/

theorem prioritized_borel_fork_decode_expand (u h : List Bool) (hlen : u.length = h.length) :
    prioritized_borel_fork_hidden_decode (prioritized_borel_fork_expand u h) = h := by
  induction u generalizing h with
  | nil => cases h <;> simp_all [prioritized_borel_fork_expand, prioritized_borel_fork_hidden_decode]
  | cons b u ih =>
      cases h with
      | nil => simp at hlen
      | cons c h =>
          have hh : u.length = h.length := by simpa using hlen
          cases c <;> simp [prioritized_borel_fork_expand, prioritized_borel_fork_three_step_block, prioritized_borel_fork_hidden_decode, ih h hh]
