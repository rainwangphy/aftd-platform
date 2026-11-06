import AFTD.Prelude

/-!
# simple_graph_ones_mem_range_imp_has_binary_vector

Topic: graphs   Node: 51c9a651c2e8

Provenance: original. Related work: arXiv:2611.08244 Thm 2.5

For any nonempty finite simple graph G on vertex set V, if the all-ones vector fun _ => 1 is in the range of Matrix.toLin' (G.adjMatrix ℝ), then there exists a non-zero (0,1)-vector in the row space of G.adjMatrix ℝ over ℝ that does not equal any row of G.adjMatrix ℝ.
-/

/-- If the all-ones vector is in the adjacency row space of a nonempty finite simple graph, it is a non-zero (0,1)-vector not occurring as a row. -/
theorem simple_graph_ones_mem_range_imp_has_binary_vector
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h1 : (fun _ : V => (1 : ℝ)) ∈ LinearMap.range (Matrix.toLin' (G.adjMatrix ℝ))) :
    ∃ y : V → ℝ, (∀ v : V, y v = 0 ∨ y v = 1) ∧ y ≠ 0 ∧
      y ∈ LinearMap.range (Matrix.toLin' (G.adjMatrix ℝ)) ∧
      ∀ u : V, y ≠ G.adjMatrix ℝ u := by
  refine ⟨fun _ => 1, fun v => Or.inr rfl, ?_, h1, ?_⟩
  · intro h
    have := congrFun h (Classical.arbitrary V)
    simp at this
  · intro u h
    have := congrFun h u
    simp [SimpleGraph.adjMatrix_apply] at this
