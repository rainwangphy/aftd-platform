import AFTD.Prelude
import AFTD.Kb.Tcs.F4Graph
import AFTD.Kb.Tcs.F4AdjBool

/-!
# f4_graph_decidable

Topic: graphs   Node: f0fa0b80193b

Provenance: helper lemma. step towards op1917_exists_nonregular_resistance_regular_order_16

Adjacency in the graph F(4) is decidable.
-/

/-- DecidableRel instance for f4_graph adjacency. -/
instance f4_graph_decidable : DecidableRel f4_graph.Adj := fun a b => inferInstanceAs (Decidable (f4_adj_bool a b = true))
