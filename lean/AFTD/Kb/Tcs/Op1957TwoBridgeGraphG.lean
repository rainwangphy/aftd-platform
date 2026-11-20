import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957TwoBridgeGraphH

/-!
# op1957_two_bridge_graph_G

Topic: graphs   Node: 9990e9631f84

Provenance: helper lemma. step towards op1957_ten_connected_first_witness_two_bridges_obstruction

The graph G of the two-bridge obstruction: the complement of H.
-/

def op1957_two_bridge_graph_G : SimpleGraph (Fin 20) := op1957_two_bridge_graph_Hᶜ
