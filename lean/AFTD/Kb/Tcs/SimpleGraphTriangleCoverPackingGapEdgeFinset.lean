import AFTD.Prelude

/-!
# simple_graph_triangle_cover_packing_gap_edge_finset

Topic: graphs   Node: fcd771624b65

Provenance: helper lemma. step towards simple_graph_minimum_triangle_cover_outside_maximum_packing_support

The 17 edges of the witness graph, listed explicitly.
-/

/-- Explicit edge list of the witness graph. -/
def simple_graph_triangle_cover_packing_gap_edge_finset : Finset (Sym2 (Fin 7)) := {Sym2.mk 0 2, Sym2.mk 0 3, Sym2.mk 0 4, Sym2.mk 0 5, Sym2.mk 0 6,
   Sym2.mk 1 4, Sym2.mk 1 5, Sym2.mk 1 6, Sym2.mk 2 3, Sym2.mk 2 4,
   Sym2.mk 2 5, Sym2.mk 2 6, Sym2.mk 3 5, Sym2.mk 3 6, Sym2.mk 4 5,
   Sym2.mk 4 6, Sym2.mk 5 6}
