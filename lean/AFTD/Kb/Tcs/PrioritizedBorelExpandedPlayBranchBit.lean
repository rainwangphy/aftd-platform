import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.Enc1385ExpandedPlay
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_expanded_play_branch_bit

Topic: automata   Node: cb3260560439

Provenance: helper lemma. Infinite-sequence encoding for arXiv:2611.10136, Conjecture 19.

The first bit of each encoded block is the direction of the corresponding original edge.
-/

theorem prioritized_borel_expanded_play_branch_bit {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (π : ℕ → TreeGameEdge Q 3) (n : ℕ) :
    (enc1385ExpandedPlay G π (n * (Fintype.card Q + 1))).dir = (π n).dir := by
  simp [enc1385ExpandedPlay, enc1385Block, Nat.mul_div_cancel n (Nat.zero_lt_succ (Fintype.card Q))]
