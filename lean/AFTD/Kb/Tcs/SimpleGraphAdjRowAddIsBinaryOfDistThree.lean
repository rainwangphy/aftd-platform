import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDisjointNeighborsOfDistThree

/-!
# simple_graph_adj_row_add_is_binary_of_dist_three

Topic: graphs   Node: 556c12540b96

Provenance: helper lemma. arXiv:2611.08244 Theorem 4.1

For two vertices at distance 3 in a finite simple graph, the sum of their rows in the adjacency matrix over ℝ is a (0,1)-vector.
-/

/-- The sum of adjacency matrix rows of two vertices at distance 3 is a (0,1)-vector. -/
theorem simple_graph_adj_row_add_is_binary_of_dist_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (hdist : G.dist u v = 3) (w : V) :
    (G.adjMatrix ℝ u + G.adjMatrix ℝ v) w = 0 ∨
    (G.adjMatrix ℝ u + G.adjMatrix ℝ v) w = 1 := by
  have hdisj := simple_graph_disjoint_neighbors_of_dist_three G u v hdist w
  simp only [Pi.add_apply, SimpleGraph.adjMatrix_apply]
  by_cases hu : G.Adj u w
  · have hv : ¬ G.Adj v w := fun h => hdisj ⟨hu, h⟩
    simp [hu, hv]
  · by_cases hv : G.Adj v w
    · simp [hu, hv]
    · simp [hu, hv]
