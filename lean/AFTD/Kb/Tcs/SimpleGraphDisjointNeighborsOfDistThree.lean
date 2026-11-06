import AFTD.Prelude

/-!
# simple_graph_disjoint_neighbors_of_dist_three

Topic: graphs   Node: b5e694dd5288

Provenance: helper lemma. arXiv:2611.08244 Theorem 4.1

In any simple graph, two vertices at distance 3 share no common neighbors.
-/

/-- Two vertices at distance 3 in a simple graph do not share any common neighbor. -/
theorem simple_graph_disjoint_neighbors_of_dist_three
    {V : Type*} (G : SimpleGraph V) (u v : V)
    (hdist : G.dist u v = 3) (w : V) :
    ¬ (G.Adj u w ∧ G.Adj v w) := by
  rintro ⟨hu, hv⟩
  have hle := G.dist_le (hu.toWalk.append hv.symm.toWalk)
  simp at hle
  omega
