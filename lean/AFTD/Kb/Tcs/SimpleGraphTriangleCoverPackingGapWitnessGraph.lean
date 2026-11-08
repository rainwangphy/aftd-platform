import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverPackingGapDeletedEdges

/-!
# simple_graph_triangle_cover_packing_gap_witness_graph

Topic: graphs   Node: 126c111940a4

Provenance: helper lemma. step towards simple_graph_minimum_triangle_cover_outside_maximum_packing_support

The seven-vertex witness graph: K7 with the edges {0,1}, {1,2}, {1,3}, {3,4} deleted (17 edges, 19 triangles).
-/

/-- Witness graph for the minimum-cover-outside-maximum-packing-support counterexample. -/
def simple_graph_triangle_cover_packing_gap_witness_graph : SimpleGraph (Fin 7) where
  Adj a b := a ≠ b ∧ Sym2.mk a b ∉ simple_graph_triangle_cover_packing_gap_deleted_edges
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩
