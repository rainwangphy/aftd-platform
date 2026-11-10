import AFTD.Prelude

/-!
# regular_adj_charpoly_root_abs_le

Topic: graphs   Node: e368a677c135

Provenance: helper lemma. arXiv:2611.00591, Lemma 4.1 (step of its proof)

For an s-regular simple graph G on a finite vertex set, every root μ of the characteristic polynomial of its real adjacency matrix satisfies |μ| ≤ s.
-/

open scoped Classical in
theorem regular_adj_charpoly_root_abs_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) (hG : G.IsRegularOfDegree s)
    (μ : ℝ) (hμ : μ ∈ (G.adjMatrix ℝ).charpoly.roots) : |μ| ≤ s := by
  have hroot : (G.adjMatrix ℝ).charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℝ)) μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, Real.dist_eq, SimpleGraph.adjMatrix_apply] at hk
  simp only [SimpleGraph.irrefl, if_false, sub_zero] at hk
  have hsum : (∑ j ∈ Finset.univ.erase k, ‖G.adjMatrix ℝ k j‖) = (s : ℝ) := by
    have h1 : (∑ j ∈ Finset.univ.erase k, ‖G.adjMatrix ℝ k j‖) =
        ∑ j, ‖G.adjMatrix ℝ k j‖ := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      simp [SimpleGraph.adjMatrix_apply]
    rw [h1]
    have h2 : ∀ j, ‖G.adjMatrix ℝ k j‖ = G.adjMatrix ℝ k j := by
      intro j
      simp only [SimpleGraph.adjMatrix_apply]
      split_ifs <;> simp
    simp only [h2]
    have h4 : (∑ j, G.adjMatrix ℝ k j) = (G.degree k : ℝ) := by
      have := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℝ) (G := G) (a := (1 : ℝ)) (v := k)
      simpa [Matrix.mulVec, dotProduct] using this
    rw [h4, hG k]
  linarith [hk, hsum.le]
