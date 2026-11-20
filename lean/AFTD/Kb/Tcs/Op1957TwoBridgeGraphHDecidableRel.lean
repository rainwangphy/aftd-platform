import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957TwoBridgeGraphH
import AFTD.Kb.Tcs.Op1957TwoBridgeGraphEdges

/-!
# op1957_two_bridge_graph_H_decidableRel

Topic: graphs   Node: 900ecc52daea

Provenance: helper lemma. step towards op1957_ten_connected_first_witness_two_bridges_obstruction

Adjacency in the 20-vertex complement graph H is decidable.
-/

instance op1957_two_bridge_graph_H_decidableRel : DecidableRel op1957_two_bridge_graph_H.Adj := fun a b => by
  change Decidable (a ≠ b ∧ ((a.val, b.val) ∈ op1957_two_bridge_graph_edges ∨
    (b.val, a.val) ∈ op1957_two_bridge_graph_edges))
  unfold op1957_two_bridge_graph_edges
  infer_instance
