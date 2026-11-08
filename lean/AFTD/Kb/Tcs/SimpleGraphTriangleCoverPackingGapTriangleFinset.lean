import AFTD.Prelude

/-!
# simple_graph_triangle_cover_packing_gap_triangle_finset

Topic: graphs   Node: b8c53da3a12f

Provenance: helper lemma. step towards simple_graph_minimum_triangle_cover_outside_maximum_packing_support

The 19 triangles of the witness graph, listed explicitly.
-/

/-- Explicit list of the triangles of the witness graph. -/
def simple_graph_triangle_cover_packing_gap_triangle_finset : Finset (Finset (Fin 7)) := {{0,2,3},{0,2,4},{0,2,5},{0,2,6},{0,3,5},{0,3,6},{0,4,5},{0,4,6},{0,5,6},
   {1,4,5},{1,4,6},{1,5,6},{2,3,5},{2,3,6},{2,4,5},{2,4,6},{2,5,6},{3,5,6},{4,5,6}}
