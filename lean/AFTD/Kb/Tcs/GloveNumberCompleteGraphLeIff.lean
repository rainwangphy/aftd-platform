import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumberLeIffHasCleanHandshakeSeq
import AFTD.Kb.Tcs.GloveNumberCompleteGraphPos
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.HandshakeEdge
import AFTD.Kb.Tcs.CleanHandshakeSeq
import AFTD.Kb.Tcs.GloveNumber

/-!
# glove_number_complete_graph_le_iff

Topic: combinatorics   Node: 4fa63bd22b7a

Provenance: helper lemma. step towards glove_number_complete_graph_open_problem

For $n \ge 2$ and every $k$, the glove number of $K_n$ is at most $k$ if and only if $K_n$ has a clean handshake sequence with $k$ gloves.
-/

/-- For `K_n`, `gl ≤ k` is equivalent to the existence of a `k`-glove covering sequence: no side condition is needed, because `gl(K_n) > 0` makes the set of admissible glove counts nonempty. -/
theorem glove_number_complete_graph_le_iff (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    glove_number (SimpleGraph.completeGraph (Fin n)) ≤ k ↔
      has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) k := by
  apply glove_number_le_iff_has_clean_handshake_seq
  have h1 := glove_number_complete_graph_pos n hn
  simp only [glove_number] at h1 ⊢
  have h : 0 < sInf {k | has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) k} := by omega
  exact Nat.nonempty_of_pos_sInf h
