import AFTD.Prelude

/-!
# root_lattice_form_det

Topic: combinatorics   Node: a89f072e768e

Provenance: helper lemma. arXiv:2610.26970 (Gaussian Lower Bounds for Distinct Subset Sums in Higher Dimensions), Proposition 3.2: the determinant claim

det(I_k − 11ᵀ/(k+1)) = 1/(k+1).
-/

theorem root_lattice_form_det (k : ℕ) :
    (1 - (1 / ((k : ℝ) + 1)) • Matrix.of (fun _ _ : Fin k => (1 : ℝ))).det = 1 / ((k : ℝ) + 1) := by
  have h : (1 - (1 / ((k : ℝ) + 1)) • Matrix.of (fun _ _ : Fin k => (1 : ℝ)))
      = 1 + Matrix.replicateCol (Fin 1) (fun _ : Fin k => -(1 / ((k : ℝ) + 1)))
          * Matrix.replicateRow (Fin 1) (fun _ : Fin k => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply]
    exact sub_eq_add_neg _ _
  have hdot : (fun _ : Fin k => (1 : ℝ)) ⬝ᵥ (fun _ : Fin k => -(1 / ((k : ℝ) + 1)))
      = (k : ℝ) * (-(1 / ((k : ℝ) + 1))) := by
    simp [dotProduct, Finset.sum_const, Fintype.card_fin]
  calc (1 - (1 / ((k : ℝ) + 1)) • Matrix.of (fun _ _ : Fin k => (1 : ℝ))).det
      = (1 + Matrix.replicateCol (Fin 1) (fun _ : Fin k => -(1 / ((k : ℝ) + 1)))
          * Matrix.replicateRow (Fin 1) (fun _ : Fin k => (1 : ℝ))).det := by rw [h]
    _ = 1 + (fun _ : Fin k => (1 : ℝ)) ⬝ᵥ (fun _ : Fin k => -(1 / ((k : ℝ) + 1))) :=
        Matrix.det_one_add_replicateCol_mul_replicateRow _ _
    _ = 1 / ((k : ℝ) + 1) := by
      rw [hdot]
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
