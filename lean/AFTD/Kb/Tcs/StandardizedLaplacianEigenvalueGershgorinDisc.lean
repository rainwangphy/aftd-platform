import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_eigenvalue_gershgorin_disc

Topic: graphs   Node: 9e9e3f33d1c4

Provenance: helper lemma. step towards op_465_standardized_laplacian_order_four_polygon_conjecture

For a standardized Laplacian matrix L of order n, every complex eigenvalue z is contained in some Gershgorin disc centred at a diagonal entry: there is a row index k with ‖z − L k k‖ ≤ L k k.
-/

theorem standardized_laplacian_eigenvalue_gershgorin_disc (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : is_standardized_laplacian n L) (z : ℂ)
    (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ))) :
    ∃ k : Fin n, ‖z - (L k k : ℂ)‖ ≤ L k k := by
  have h1 : z ∈ spectrum ℂ (Matrix.toLin' (L.map (algebraMap ℝ ℂ))) := by
    rw [Matrix.spectrum_toLin']
    exact hz
  have h2 := Module.End.HasEigenvalue.of_mem_spectrum h1
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball h2
  use k
  have hk' : ‖z - (L.map (algebraMap ℝ ℂ) k k)‖ ≤ ∑ j ∈ Finset.univ.erase k, ‖(L.map (algebraMap ℝ ℂ)) k j‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    exact hk
  have h_diag : (L.map (algebraMap ℝ ℂ)) k k = (L k k : ℂ) := rfl
  rw [h_diag] at hk'
  have h_rad : ∑ j ∈ Finset.univ.erase k, ‖(L.map (algebraMap ℝ ℂ)) k j‖ = L k k := by
    have h_row := hL.1 k
    have h_off := hL.2
    have h_norm : ∀ j ∈ Finset.univ.erase k, ‖(L.map (algebraMap ℝ ℂ)) k j‖ = - L k j := by
      intro j hj
      have h_ne : k ≠ j := (Finset.ne_of_mem_erase hj).symm
      have h_le : L k j ≤ 0 := (h_off k j h_ne).2
      have : (L.map (algebraMap ℝ ℂ)) k j = (L k j : ℂ) := rfl
      rw [this, Complex.norm_real, Real.norm_of_nonpos h_le]
    rw [Finset.sum_congr rfl h_norm]
    rw [Finset.sum_neg_distrib]
    have h_split : L k k + ∑ j ∈ Finset.univ.erase k, L k j = ∑ j, L k j :=
      Finset.add_sum_erase Finset.univ (fun j => L k j) (Finset.mem_univ k)
    linarith
  rw [h_rad] at hk'
  exact hk'
