import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphV3
import AFTD.Kb.Tcs.MaxDegreeLeTwoExistsRichNeighborFiveColoring

/-!
# op_310_partial_empty_V3

Topic: graphs   Node: 0f806243ea7a

Provenance: original. Related work: arXiv:2610.21868 Sec. 4

Every subcubic finite simple graph with no degree-3 vertices admits a rich-neighbor 5-edge-coloring.
-/

/-- Every subcubic finite simple graph with no degree-3 vertices admits a rich-neighbor 5-edge-coloring. -/
theorem op_310_partial_empty_V3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 3)
    (hV3 : simple_graph_V3 G = ∅) :
    ∃ c : G.lineGraph.Coloring (Fin 5), simple_graph_is_rich_neighbor_coloring G c := by
  have h2 : G.maxDegree ≤ 2 := by
    apply G.maxDegree_le_of_forall_degree_le 2
    intro v
    have hle : G.degree v ≤ 3 := (G.degree_le_maxDegree v).trans hdeg
    have hne : G.degree v ≠ 3 := by
      intro heq
      have hv : v ∈ simple_graph_V3 G := by
        rw [simple_graph_V3, Finset.mem_filter]
        exact ⟨Finset.mem_univ v, heq⟩
      rw [hV3] at hv
      simp at hv
    omega
  exact maxDegree_le_two_exists_rich_neighbor_five_coloring G h2
