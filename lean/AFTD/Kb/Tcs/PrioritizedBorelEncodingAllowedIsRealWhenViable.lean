import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_encoding_allowed_is_real_when_viable

Topic: automata   Node: d23523ba8a53

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

When a real encoding move exists, every allowed move is real and the fallback cannot be used.
-/

theorem prioritized_borel_encoding_allowed_is_real_when_viable {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (s : Enc1385State Q) (bit : Bool) (prio : Fin 3) (hv : ∃ bit' prio', enc1385Real G s bit' prio') (ha : enc1385Allowed G s bit prio) : enc1385Real G s bit prio := by
  rcases ha with h | ⟨hnot, -⟩
  · exact h
  · contradiction
