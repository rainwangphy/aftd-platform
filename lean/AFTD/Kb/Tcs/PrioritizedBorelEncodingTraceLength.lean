import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Trace
import AFTD.Kb.Tcs.PrioritizedBorelEncodingStateCodeLength
import AFTD.Kb.Tcs.Enc1385Game

/-!
# prioritized_borel_encoding_trace_length

Topic: automata   Node: f1795a581a19

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

An encoded state history has one fixed-length block per original edge.
-/

theorem prioritized_borel_encoding_trace_length {Q : Type} [Fintype Q] (v : List Bool) (h : Fin (v.length + 1) → Q) : (enc1385Trace v h).length = v.length * (Fintype.card Q + 1) := by
  dsimp [enc1385Trace]
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  simp [prioritized_borel_encoding_state_code_length]
