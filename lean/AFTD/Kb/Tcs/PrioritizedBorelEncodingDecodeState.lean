import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.PrioritizedBorelEncodingStateCodeInjective
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_encoding_decode_state

Topic: automata   Node: ed4206fa6734

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

Decoding a valid one-hot state code recovers the original state.
-/

theorem prioritized_borel_encoding_decode_state {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (q : Q) : enc1385Decode G (enc1385StateCode q) = q := by
  classical
  have h : ∃ r : Q, enc1385StateCode r = enc1385StateCode q := ⟨q,rfl⟩
  unfold enc1385Decode
  rw [dif_pos h]
  exact prioritized_borel_encoding_state_code_injective (Classical.choose_spec h)
