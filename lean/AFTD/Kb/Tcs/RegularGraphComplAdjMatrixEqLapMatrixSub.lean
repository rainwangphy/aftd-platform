import AFTD.Prelude

/-!
# regular_graph_compl_adj_matrix_eq_lap_matrix_sub

Topic: graphs   Node: 6d4573b7b47b

Provenance: helper lemma. arXiv:2610.36127 Proof of Lemma 35

For any d-regular graph G on a finite vertex set V, the adjacency matrix of its complement Gᶜ equals G.lapMatrix ℝ - ((d+1)I - J), where J is the all-ones matrix.
-/

open scoped Classical in
/-- The adjacency matrix of the complement of a d-regular graph equals L(G) - ((d+1)I - J). -/
theorem regular_graph_compl_adj_matrix_eq_lap_matrix_sub
    {V : Type*} [Fintype V] (d : ℕ) (G : SimpleGraph V)
    (hreg : G.IsRegularOfDegree d) :
    Gᶜ.adjMatrix ℝ =
      G.lapMatrix ℝ - ((d + 1 : ℝ) • (1 : Matrix V V ℝ) - Matrix.of fun (_ _ : V) ↦ (1 : ℝ)) := by
  ext u v
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, Matrix.diagonal_apply]
  rw [hreg u]
  by_cases h : u = v
  · subst h
    simp
  · simp [h]
    split_ifs <;> ring
