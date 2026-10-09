import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount

/-!
# simple_graph_leaf_neighbor_count_complete_two

Topic: graphs   Node: 59c20311335c

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11446 (On the local average order of dominating sets).

In K₂, each vertex has exactly one leaf neighbour.
-/

theorem simple_graph_leaf_neighbor_count_complete_two :
    simple_graph_leaf_neighbor_count (⊤ : SimpleGraph (Fin 2)) 0 = 1 := by
  unfold simple_graph_leaf_neighbor_count; decide
