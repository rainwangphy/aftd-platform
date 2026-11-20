import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957TwoBridgeGraphG
import AFTD.Kb.Tcs.Op1957TwoBridgeGraphHDecidableRel
import AFTD.Kb.Tcs.Op1957TwoBridgeGraphH

/-!
# op1957_two_bridge_graph_G_decidableRel

Topic: graphs   Node: f674c1b88b71

Provenance: helper lemma. step towards op1957_ten_connected_first_witness_two_bridges_obstruction

Adjacency in the graph G is decidable.
-/

instance op1957_two_bridge_graph_G_decidableRel : DecidableRel op1957_two_bridge_graph_G.Adj := inferInstanceAs (DecidableRel (op1957_two_bridge_graph_Hᶜ).Adj)
