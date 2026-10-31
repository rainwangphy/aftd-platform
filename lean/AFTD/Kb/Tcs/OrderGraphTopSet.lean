import AFTD.Prelude
import AFTD.Kb.Tcs.Order

/-!
# order_graph_top_set

Topic: combinatorics   Node: ed2b6cb12d34

Provenance: helper lemma. step towards order_graph_edges_ge_lower_bound

For an edge e = (ν, a) and a level m, the top set U_m(e) is the set consisting of a together with the first m-1 labels of ν.
-/

/-- The m-element label set determined by an edge: its label plus the first m-1 labels of its order. -/
def order_graph_top_set {d : ℕ} (m : ℕ) (e : Order d × Fin d) : Finset (Fin d) := insert e.2 (List.take (m - 1) e.1.elems).toFinset
