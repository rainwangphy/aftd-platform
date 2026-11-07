import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeOrderCode
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# edge_order_code_top_two

Topic: approximation   Node: 90e14e7424e8

Provenance: helper lemma. Sanity check of edge_order_code (OP-851 encoding).

The order consisting of the single edge {1, 0} of the complete graph on two vertices is encoded as false (endpoint 0), then true, true, false (endpoint 1).
-/

theorem edge_order_code_top_two :
    edge_order_code [(⟨s(1, 0), by simp⟩ : (⊤ : SimpleGraph (Fin 2)).edgeSet)] =
      [false, true, true, false] := by
  decide
