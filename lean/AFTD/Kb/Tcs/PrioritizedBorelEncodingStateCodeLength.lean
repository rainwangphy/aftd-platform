import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game

/-!
# prioritized_borel_encoding_state_code_length

Topic: automata   Node: b10f7358f193

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

The one-hot code of a state has length equal to the number of states.
-/

theorem prioritized_borel_encoding_state_code_length {Q : Type} [Fintype Q] (q : Q) : (enc1385StateCode q).length = Fintype.card Q := by
  simp [enc1385StateCode]
