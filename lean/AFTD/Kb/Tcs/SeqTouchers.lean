import AFTD.Prelude
import AFTD.Kb.Tcs.HandshakeTouchers
import AFTD.Kb.Tcs.Handshake

/-!
# seq_touchers

Topic: combinatorics   Node: 1b79a84116f0

Provenance: helper lemma. step towards glove_number_k4

The set of vertices that directly touch the glove side `s` at some handshake of the sequence `seq` (the union of the touch sets of the individual handshakes).
-/

/-- The set of all vertices that directly touch the glove side `s` somewhere in `seq`. -/
def seq_touchers {V : Type*} {Γ : Type*} [DecidableEq Γ] (seq : List (Handshake V Γ)) (s : Γ × Bool) : Set V := seq.foldr (fun h acc => handshake_touchers h s ∪ acc) ∅
