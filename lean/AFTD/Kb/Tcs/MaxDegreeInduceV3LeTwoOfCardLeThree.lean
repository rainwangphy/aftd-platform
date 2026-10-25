import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphV3
import AFTD.Kb.Tcs.MaxDegreeInduceV3LeTwoIff

/-!
# maxDegree_induce_V3_le_two_of_card_le_three

Topic: graphs   Node: fc3818e86d5f

Provenance: helper lemma. folklore

For any finite simple graph G, if the number of vertices of degree 3 in G is at most 3, then the induced subgraph on the set of degree-3 vertices has maximum degree at most 2.
-/

/-- If a finite simple graph has at most three vertices of degree 3, then the induced subgraph on its degree-3 vertices has maximum degree at most 2. -/
theorem maxDegree_induce_V3_le_two_of_card_le_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : (simple_graph_V3 G).card ≤ 3) :
    (G.induce (simple_graph_V3 G : Set V)).maxDegree ≤ 2 := by
  rw [maxDegree_induce_V3_le_two_iff]
  intro v
  have h1 := (G.induce (simple_graph_V3 G : Set V)).degree_lt_card_verts v
  simp only [SetLike.coe_sort_coe, Fintype.card_coe] at h1
  omega
