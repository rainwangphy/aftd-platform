import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount

/-!
# simple_graph_is_star_like_complete_two

Topic: graphs   Node: 530619c0b10d

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11446 (On the local average order of dominating sets).

K₂ is star-like.
-/

theorem simple_graph_is_star_like_complete_two : simple_graph_is_star_like (⊤ : SimpleGraph (Fin 2)) := by
  unfold simple_graph_is_star_like simple_graph_leaf_neighbor_count; decide
