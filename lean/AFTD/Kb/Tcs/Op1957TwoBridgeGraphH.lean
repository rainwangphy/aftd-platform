import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957TwoBridgeGraphEdges

/-!
# op1957_two_bridge_graph_H

Topic: graphs   Node: b4a420ab3fb7

Provenance: helper lemma. step towards op1957_ten_connected_first_witness_two_bridges_obstruction

The complement graph H of the two-bridge obstruction on 20 vertices, defined from its edge list.
-/

def op1957_two_bridge_graph_H : SimpleGraph (Fin 20) where
  Adj a b := a ≠ b ∧ ((a.val, b.val) ∈ op1957_two_bridge_graph_edges ∨
    (b.val, a.val) ∈ op1957_two_bridge_graph_edges)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩
