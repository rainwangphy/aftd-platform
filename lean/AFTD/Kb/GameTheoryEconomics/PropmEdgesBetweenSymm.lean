import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EdgesBetween

/-!
# propm_edges_between_symm

Topic: fair_division   Node: 497204d42247

Parallel classes are symmetric: the edges between i and j are the edges between j and i.
-/

/-- Parallel classes are symmetric. -/
lemma propm_edges_between_symm {m n : ℕ} (ends : Fin m → Fin n × Fin n) (i j : Fin n) :
    edges_between ends i j = edges_between ends j i := by
  ext e; simp only [edges_between, Finset.mem_filter, Finset.mem_univ, true_and]; exact or_comm
