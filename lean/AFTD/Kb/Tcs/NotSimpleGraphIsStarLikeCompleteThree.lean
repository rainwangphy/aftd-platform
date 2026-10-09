import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount

/-!
# not_simple_graph_is_star_like_complete_three

Topic: graphs   Node: d860e89efcc9

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11446 (On the local average order of dominating sets).

K₃ is not star-like (no vertex is a leaf or has a leaf neighbour).
-/

theorem not_simple_graph_is_star_like_complete_three :
    ¬ simple_graph_is_star_like (⊤ : SimpleGraph (Fin 3)) := by
  unfold simple_graph_is_star_like simple_graph_leaf_neighbor_count; decide
