import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumberK2
import AFTD.Kb.Tcs.GloveNumberK3
import AFTD.Kb.Tcs.GloveNumber

/-!
# glove_number_complete_graph_le_three

Topic: combinatorics   Node: e1279cf58bf6

Provenance: helper lemma. arXiv:2610.17602 line 348 -- Clean handshake sequences

For any integer $n$ such that $2 \\le n \\le 3$, the glove number of the complete graph $K_n$ is equal to $n - 1$.
-/

/-- The glove number of K_n equals n - 1 for n = 2 and n = 3. -/
theorem glove_number_complete_graph_le_three (n : ℕ) (h2 : 2 ≤ n) (h3 : n ≤ 3) :
    glove_number (SimpleGraph.completeGraph (Fin n)) = n - 1 := by
  interval_cases n
  · exact glove_number_k2
  · exact glove_number_k3
