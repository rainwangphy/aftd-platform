import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraphIsNetRegular
import AFTD.Kb.Tcs.SignedGraphNetDegree
import AFTD.Kb.Tcs.SignedGraph

/-!
# signed_graph_isNetRegular_of_netDegree_eq

Topic: combinatorics   Node: f85960229dd7

Provenance: helper lemma. arXiv:2611.13901 Section 3.2

If every vertex v of a finite signed graph G has net-degree equal to a constant integer d, then G is net-regular.
-/

/-- A signed graph is net-regular if all vertices have net-degree equal to d. -/
theorem signed_graph_isNetRegular_of_netDegree_eq {V : Type*} [Fintype V] (G : SignedGraph V) (d : ℤ) (h : ∀ v : V, G.netDegree v = d) : G.IsNetRegular := ⟨d, h⟩
