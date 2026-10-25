import AFTD.Prelude
import AFTD.Kb.Tcs.MaxDegreeInduceV3LeTwoIffNeighborFilter
import AFTD.Kb.Tcs.SubcubicSubgraphThreeVerticesMaxDegreeLeTwo
import AFTD.Kb.Tcs.SimpleGraphV3

/-!
# subcubic_induce_V3_maxDegree_le_two_subgraph

Topic: graphs   Node: 7f9d0edde7a1

Provenance: helper lemma. step towards subcubic_maxDegree_induce_V3_le_two_exists_rich_neighbor_five_coloring

If H is a subgraph of G, G is subcubic, and the induced subgraph on V3(G) has maximum degree at most 2, then H is also subcubic and the induced subgraph on V3(H) has maximum degree at most 2.
-/

/-- Subgraphs of a subcubic graph whose degree-3 vertices induce a subgraph of maximum degree at most 2 also satisfy both properties. -/
theorem subcubic_induce_V3_maxDegree_le_two_subgraph {V : Type*}
    [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G)
    (hdeg : G.maxDegree ≤ 3)
    (h3 : (G.induce (simple_graph_V3 G : Set V)).maxDegree ≤ 2) :
    H.maxDegree ≤ 3 ∧ (H.induce (simple_graph_V3 H : Set V)).maxDegree ≤ 2 := by
  have h3' : ∀ v, G.degree v = 3 → ((G.neighborFinset v).filter (fun w => G.degree w = 3)).card ≤ 2 :=
    (maxDegree_induce_V3_le_two_iff_neighbor_filter G).mp h3
  obtain ⟨hd, h3H⟩ := subcubic_subgraph_three_vertices_max_degree_le_two G H hHG hdeg h3'
  exact ⟨hd, (maxDegree_induce_V3_le_two_iff_neighbor_filter H).mpr h3H⟩
