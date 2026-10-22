import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberDeleteEdgeLe
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberMono
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_cover_number_le_two_mul_packing_number_of_decreasing_edge

Topic: graphs   Node: d782592aa3be

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

Induction step for the easy branch: if every graph on the same vertex type with strictly smaller triangle packing number satisfies τ ≤ 2ν, and deleting some edge e from G strictly lowers ν, then τ(G) ≤ 2ν(G).
-/

/-- The ν-decreasing branch of the induction on ν: one edge deletion plus the induction hypothesis gives τ(G) ≤ 2ν(G). -/
theorem simple_graph_triangle_cover_number_le_two_mul_packing_number_of_decreasing_edge
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph V,
      simple_graph_triangle_packing_number H < simple_graph_triangle_packing_number G →
      simple_graph_triangle_cover_number H ≤ 2 * simple_graph_triangle_packing_number H)
    (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hdec : simple_graph_triangle_packing_number (G.deleteEdges {e}) <
      simple_graph_triangle_packing_number G) :
    simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
  have h1 := simple_graph_triangle_cover_number_delete_edge_le G e he
  have h2 := hIH (G.deleteEdges {e}) hdec
  omega
