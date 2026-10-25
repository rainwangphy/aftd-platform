import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SubcubicIsAcyclicExistsStrongFiveEdgeColoring
import AFTD.Kb.Tcs.SubcubicIsAcyclicExistsLeafEdgeDistTwoLeFour
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoringOfForallRich
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# subcubic_isAcyclic_exists_rich_neighbor_five_coloring

Topic: graphs   Node: 7324727b9c17

Provenance: helper lemma. step towards subcubic_three_vertices_max_degree_le_one_exists_rich_neighbor_five_coloring

Every subcubic acyclic finite simple graph admits a rich-neighbor 5-edge-colouring.
-/

/-- Base case of Lemma 2.2: any subcubic forest admits a rich-neighbor 5-edge-coloring. -/
theorem subcubic_isAcyclic_exists_rich_neighbor_five_coloring {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 3)
    (hforest : G.IsAcyclic) :
    ∃ c : G.lineGraph.Coloring (Fin 5), simple_graph_is_rich_neighbor_coloring G c := by
  obtain ⟨c, hc⟩ := subcubic_isAcyclic_exists_strong_five_edge_coloring G hdeg hforest
  exact ⟨c, simple_graph_is_rich_neighbor_coloring_of_forall_rich G c hc⟩
