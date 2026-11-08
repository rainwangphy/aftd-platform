import AFTD.Prelude

/-!
# simple_graph_triangle_cover_packing_gap_deleted_edges

Topic: graphs   Node: f94112bc50f6

Provenance: helper lemma. step towards simple_graph_minimum_triangle_cover_outside_maximum_packing_support

The four edges deleted from K7 to build the witness graph: {0,1}, {1,2}, {1,3}, {3,4}.
-/

/-- The four edges removed from K7 in the witness graph. -/
def simple_graph_triangle_cover_packing_gap_deleted_edges : Finset (Sym2 (Fin 7)) := {Sym2.mk 0 1, Sym2.mk 1 2, Sym2.mk 1 3, Sym2.mk 3 4}
