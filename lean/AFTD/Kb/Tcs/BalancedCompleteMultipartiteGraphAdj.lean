import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedCompleteMultipartiteGraph

/-!
# balanced_complete_multipartite_graph_adj

Topic: graphs   Node: 67fdb6e9edca

Provenance: helper lemma. sanity lemma for balanced_complete_multipartite_graph (OP-546)

In balanced_complete_multipartite_graph r n, u and v are adjacent iff u / n ≠ v / n.
-/

theorem balanced_complete_multipartite_graph_adj (r n : ℕ) (u v : Fin (r * n)) :
    (balanced_complete_multipartite_graph r n).Adj u v ↔ (u : ℕ) / n ≠ (v : ℕ) / n := Iff.rfl
