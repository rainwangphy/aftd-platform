import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game

/-!
# enc1385Trace

Topic: automata   Node: e9388b5a0481

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

Encode a visible node and its state history as successive blocks, each containing the visible direction followed by the one-hot code of the next state.
-/

noncomputable def enc1385Trace {Q : Type} [Fintype Q] (v : List Bool) (h : Fin (v.length + 1) → Q) : List Bool := (List.ofFn (fun i : Fin v.length => v.get i :: enc1385StateCode (h i.succ))).flatten
