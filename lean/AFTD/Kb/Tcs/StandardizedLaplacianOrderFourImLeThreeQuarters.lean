import AFTD.Prelude
import AFTD.Kb.Tcs.StandardizedLaplacianEigenvalueGershgorinDisc
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_order_four_im_le_three_quarters

Topic: graphs   Node: e27c1910d6ca

Provenance: helper lemma. step towards op_465_standardized_laplacian_order_four_polygon_conjecture

For any standardized Laplacian matrix L of order 4, the imaginary part of every complex eigenvalue z satisfies |Im z| ≤ 3/4.
-/

theorem standardized_laplacian_order_four_im_le_three_quarters (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian 4 L) (z : ℂ)
    (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ))) :
    |z.im| ≤ (3 : ℝ) / 4 := by
  obtain ⟨k, hk⟩ := standardized_laplacian_eigenvalue_gershgorin_disc 4 L hL z hz
  have h_im_le : |z.im| ≤ ‖z - (L k k : ℂ)‖ := by
    have h_im_eq : z.im = (z - (L k k : ℂ)).im := by
      simp [Complex.sub_im, Complex.ofReal_im]
    rw [h_im_eq]
    exact Complex.abs_im_le_norm (z - (L k k : ℂ))
  have h_diag_le : L k k ≤ (3 : ℝ) / 4 := by
    have h_row := hL.1 k
    have h_off := hL.2
    have h_split : L k k + ∑ j ∈ Finset.univ.erase k, L k j = ∑ j, L k j :=
      Finset.add_sum_erase Finset.univ (fun j => L k j) (Finset.mem_univ k)
    rw [h_row] at h_split
    have h_diag : L k k = ∑ j ∈ Finset.univ.erase k, -L k j := by
      rw [Finset.sum_neg_distrib]
      linarith
    rw [h_diag]
    have h_le : ∀ j ∈ Finset.univ.erase k, -L k j ≤ (1 : ℝ) / 4 := by
      intro j hj
      have h_ne : k ≠ j := (Finset.ne_of_mem_erase hj).symm
      have := (h_off k j h_ne).1
      linarith
    have h_sum_le := Finset.sum_le_sum h_le
    have h_card : (Finset.univ.erase k).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
      simp
    have h_const : ∑ j ∈ Finset.univ.erase k, ((1 : ℝ) / 4) = (3 : ℝ) / 4 := by
      rw [Finset.sum_const, h_card, nsmul_eq_mul]
      ring
    linarith
  linarith
