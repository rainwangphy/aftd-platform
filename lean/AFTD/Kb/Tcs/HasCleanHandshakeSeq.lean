import AFTD.Prelude
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.CleanHandshakeSeq

/-!
# has_clean_handshake_seq

Topic: combinatorics   Node: 70a0c417777a

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:222

A simple graph $G$ has a clean handshake sequence with $k$ gloves if there exists a sequence of handshakes over glove type $\mathrm{Fin}(k)$ that is clean starting from the empty contamination map and covers every edge of $G$.
-/

/-- Whether a graph admits a clean handshake sequence using k gloves. -/
def has_clean_handshake_seq {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop := ∃ seq : List (Handshake V (Fin k)),
    CleanHandshakeSeq seq (fun _ => ∅) ∧
    ∀ e ∈ G.edgeSet, ∃ h ∈ seq, handshake_edge h = e
