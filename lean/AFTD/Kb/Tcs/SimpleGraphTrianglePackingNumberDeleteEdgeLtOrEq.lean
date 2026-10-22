import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberMono

/-!
# simple_graph_triangle_packing_number_delete_edge_lt_or_eq

Topic: graphs   Node: 7d74f1403cc0

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

For every finite graph G, either some single-edge deletion strictly decreases the triangle packing number, or every single-edge deletion preserves it.
-/

/-- Dichotomy of edge deletions for the triangle packing number: either one deletion drops it, or all deletions preserve it. -/
theorem simple_graph_triangle_packing_number_delete_edge_lt_or_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    (∃ e ∈ G.edgeSet,
      simple_graph_triangle_packing_number (G.deleteEdges {e}) <
        simple_graph_triangle_packing_number G) ∨
    (∀ e ∈ G.edgeSet,
      simple_graph_triangle_packing_number (G.deleteEdges {e}) =
        simple_graph_triangle_packing_number G) := by
  by_cases h : ∃ e ∈ G.edgeSet, simple_graph_triangle_packing_number (G.deleteEdges {e}) < simple_graph_triangle_packing_number G
  · exact Or.inl h
  · right
    intro e he
    have hle : simple_graph_triangle_packing_number (G.deleteEdges {e}) ≤ simple_graph_triangle_packing_number G :=
      simple_graph_triangle_packing_number_mono G (G.deleteEdges {e}) (SimpleGraph.deleteEdges_le {e})
    have hnot : ¬ (simple_graph_triangle_packing_number (G.deleteEdges {e}) < simple_graph_triangle_packing_number G) :=
      fun hlt => h ⟨e, he, hlt⟩
    omega
