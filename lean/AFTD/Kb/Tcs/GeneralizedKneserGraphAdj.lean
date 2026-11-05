import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedKneserGraph

/-!
# generalized_kneser_graph_adj

Topic: graphs   Node: f5cc570006d1

Provenance: helper lemma. arXiv:2611.04486 Sec. 1

In the generalized Kneser graph KG(2n, n, r), two vertices s and t are adjacent if and only if s ≠ t and the cardinality of their intersection s.1 ∩ t.1 is strictly less than r.
-/

/-- Adjacency criterion for the generalized Kneser graph KG(2n, n, r). -/
theorem generalized_kneser_graph_adj (n r : ℕ)
    (s t : {s : Finset (Fin (2 * n)) // s.card = n}) :
    (generalized_kneser_graph n r).Adj s t ↔ s ≠ t ∧ (s.1 ∩ t.1).card < r := Iff.rfl
