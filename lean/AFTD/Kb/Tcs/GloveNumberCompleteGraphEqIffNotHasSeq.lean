import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumberCompleteGraphEqIffGe
import AFTD.Kb.Tcs.GloveNumberCompleteGraphLeIff
import AFTD.Kb.Tcs.HasCleanHandshakeSeq
import AFTD.Kb.Tcs.GloveNumber

/-!
# glove_number_complete_graph_eq_iff_not_has_seq

Topic: combinatorics   Node: f1cd5ebd601f

Provenance: helper lemma. arXiv:2610.17602 -- Clean handshake sequences

For any integer $n \\ge 2$, the glove number of the complete graph $K_n$ is equal to $n - 1$ if and only if no clean handshake sequence using $n - 2$ gloves covers all edges of $K_n$.
-/

/-- For any integer n ≥ 2, the glove number of K_n is n - 1 if and only if there is no clean handshake sequence covering K_n using n - 2 gloves. -/
theorem glove_number_complete_graph_eq_iff_not_has_seq (n : ℕ) (hn : 2 ≤ n) :
    glove_number (SimpleGraph.completeGraph (Fin n)) = n - 1 ↔
    ¬ has_clean_handshake_seq (SimpleGraph.completeGraph (Fin n)) (n - 2) := by
  rw [glove_number_complete_graph_eq_iff_ge n hn,
    ← glove_number_complete_graph_le_iff n hn (n - 2)]
  omega
