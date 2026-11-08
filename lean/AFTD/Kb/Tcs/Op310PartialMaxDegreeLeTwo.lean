import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphV3
import AFTD.Kb.Tcs.MaxDegreeLeTwoExistsRichNeighborFiveColoring
import AFTD.Kb.Tcs.MaxDegreeInduceV3LeTwoOfCardLeThree

/-!
# op_310_partial_maxDegree_le_two

Topic: graphs   Node: 428845920c63

Provenance: original. Related work: arXiv:2610.21868 Sec. 4

Every finite simple graph with maximum degree at most 2 satisfies the Delta(G[V_3]) <= 2 condition and admits a rich-neighbor 5-edge-coloring.
-/

/-- Every finite simple graph with maximum degree at most 2 has Delta(G[V3]) <= 2 and admits a rich-neighbor 5-edge-coloring. -/
theorem op_310_partial_maxDegree_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 2) :
    (G.induce (simple_graph_V3 G : Set V)).maxDegree ≤ 2 ∧
      ∃ c : G.lineGraph.Coloring (Fin 5), simple_graph_is_rich_neighbor_coloring G c := by
  refine ⟨?_, maxDegree_le_two_exists_rich_neighbor_five_coloring G hdeg⟩
  apply maxDegree_induce_V3_le_two_of_card_le_three
  have h_empty : simple_graph_V3 G = ∅ := by
    rw [simple_graph_V3, Finset.filter_eq_empty_iff]
    intro v _ hv
    have := G.degree_le_maxDegree v
    omega
  rw [h_empty]
  simp
