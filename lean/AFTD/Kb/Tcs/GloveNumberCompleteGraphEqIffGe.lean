import AFTD.Prelude
import AFTD.Kb.Tcs.GloveNumber
import AFTD.Kb.Tcs.GloveNumberCompleteGraphUpperBound

/-!
# glove_number_complete_graph_eq_iff_ge

Topic: combinatorics   Node: 162a43ed1159

Provenance: helper lemma. arXiv:2610.17602 Theorem 3 (Clean handshake sequences)

For any integer $n \ge 2$, the glove number of the complete graph $K_n$ is equal to $n - 1$ if and only if it is at least $n - 1$.
-/

/-- For n ≥ 2, the glove number of K_n is equal to n - 1 if and only if it is at least n - 1. -/
theorem glove_number_complete_graph_eq_iff_ge (n : ℕ) (hn : 2 ≤ n) :
    glove_number (SimpleGraph.completeGraph (Fin n)) = n - 1 ↔
    n - 1 ≤ glove_number (SimpleGraph.completeGraph (Fin n)) := by
  have h := glove_number_complete_graph_upper_bound n hn
  constructor
  · intro heq
    rw [heq]
  · intro hle
    exact le_antisymm h hle
