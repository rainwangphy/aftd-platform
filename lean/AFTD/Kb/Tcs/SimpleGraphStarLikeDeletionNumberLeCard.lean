import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarLikeDeletionNumber
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount

/-!
# simple_graph_star_like_deletion_number_le_card

Topic: graphs   Node: 02f5c2b80d6a

Provenance: helper lemma. arXiv:2208.10475v2: The average size of a dominating set in a graph

For every finite simple graph G, deleting all vertices leaves the empty graph, which is star-like, so the star-like deletion number d_*(G) is at most the number of vertices of G.
-/

/-- The star-like deletion number of G is at most the total number of vertices |V|. -/
theorem simple_graph_star_like_deletion_number_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    simple_graph_star_like_deletion_number G ≤ Fintype.card V := by
  unfold simple_graph_star_like_deletion_number
  apply Nat.sInf_le
  refine ⟨Finset.univ, ?_, by simp⟩
  intro w
  exact absurd w.2 (by simp)
