import AFTD.Prelude
import AFTD.Kb.Tcs.HasCleanHandshakeSeqSucc
import AFTD.Kb.Tcs.HasCleanHandshakeSeq

/-!
# has_clean_handshake_seq_mono

Topic: combinatorics   Node: 3c8d270671de

Provenance: helper lemma. step towards glove_number_complete_graph_open_problem

If a graph $G$ admits a clean handshake sequence with $k$ gloves and $k \le k'$, then it admits one with $k'$ gloves.
-/

/-- Glove counts admitting a covering sequence form an upward closed set. -/
theorem has_clean_handshake_seq_mono {V : Type*} (G : SimpleGraph V) {k k' : ℕ} (hkk : k ≤ k')
    (h : has_clean_handshake_seq G k) : has_clean_handshake_seq G k' := by
  induction hkk with
  | refl => exact h
  | step hkk ih => exact has_clean_handshake_seq_succ G _ ih
