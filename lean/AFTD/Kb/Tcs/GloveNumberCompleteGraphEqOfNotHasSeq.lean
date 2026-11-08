import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumberCompleteGraphEqIffNotHasSeq
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.GloveNumber

/-!
# glove_number_complete_graph_eq_of_not_has_seq

Topic: combinatorics   Node: a848771758dc

Provenance: helper lemma. arXiv:2610.17602 -- Clean handshake sequences

For any integer $n \\ge 2$, if no clean handshake sequence using $n - 2$ gloves covers all edges of $K_n$, then the glove number of $K_n$ is equal to $n - 1$.
-/

/-- If no clean handshake sequence with n - 2 gloves covers all edges of K_n, then the glove number of K_n equals n - 1. -/
theorem glove_number_complete_graph_eq_of_not_has_seq (n : ℕ) (hn : 2 ≤ n)
    (h : ¬ has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) (n - 2)) :
    glove_number (SimpleGraph.completeGraph (Fin n)) = n - 1 := by
  exact (glove_number_complete_graph_eq_iff_not_has_seq n hn).mpr h
