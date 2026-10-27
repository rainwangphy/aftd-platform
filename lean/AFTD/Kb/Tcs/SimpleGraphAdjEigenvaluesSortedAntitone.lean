import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAdjEigenvaluesSorted
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# simple_graph_adj_eigenvalues_sorted_antitone

Topic: graphs   Node: 96912bd19d64

Provenance: helper lemma. sanity lemma for simple_graph_adj_eigenvalues_sorted (OP-546)

The sorted adjacency eigenvalues of a finite simple graph are nonincreasing in the index.
-/

theorem simple_graph_adj_eigenvalues_sorted_antitone {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Antitone (simple_graph_adj_eigenvalues_sorted G) := by
  unfold simple_graph_adj_eigenvalues_sorted
  exact Matrix.IsHermitian.eigenvalues₀_antitone _
