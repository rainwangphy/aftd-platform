import AFTD.Prelude

/-!
# simple_graph_adj_row_add_mem_range

Topic: graphs   Node: e52cfe6b207f

Provenance: helper lemma. arXiv:2611.08244 Theorem 4.1

For any two vertices u and v of a finite simple graph, the sum of their adjacency matrix rows lies in the row space (the range of the adjacency matrix linear map) over ℝ.
-/

/-- The sum of two rows of the adjacency matrix belongs to the range of the adjacency matrix linear map. -/
theorem simple_graph_adj_row_add_mem_range
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    G.adjMatrix ℝ u + G.adjMatrix ℝ v ∈ LinearMap.range (Matrix.toLin' (G.adjMatrix ℝ)) := by
  set A : Matrix V V ℝ := G.adjMatrix ℝ
  have hsymm : A.IsSymm := SimpleGraph.isSymm_adjMatrix G
  have hrow : ∀ w : V, A w = A.mulVec (Pi.single w 1) := by
    intro w
    rw [Matrix.mulVec_single_one]
    funext i
    exact hsymm.apply i w
  rw [hrow u, hrow v]
  rw [← Matrix.toLin'_apply, ← Matrix.toLin'_apply]
  rw [← LinearMap.map_add]
  exact LinearMap.mem_range_self _ _
