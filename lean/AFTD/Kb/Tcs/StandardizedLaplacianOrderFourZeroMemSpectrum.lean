import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# standardized_laplacian_order_four_zero_mem_spectrum

Topic: graphs   Node: 1020579e31ef

Provenance: helper lemma. arXiv:2610.14100 Sec. 2

For every standardized Laplacian matrix L of order 4, zero is an eigenvalue of L.
-/

/-- Zero is an eigenvalue of every standardized Laplacian matrix of order 4. -/
theorem standardized_laplacian_order_four_zero_mem_spectrum (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian 4 L) :
    (0 : ℂ) ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)) := by
  open Matrix in
  rw [spectrum.mem_iff]
  simp only [map_zero, zero_sub, IsUnit.neg_iff]
  intro hUnit
  have hMv : (L.map (algebraMap ℝ ℂ)) *ᵥ (fun _ => (1 : ℂ)) = 0 := by
    ext i
    simp only [mulVec, dotProduct, Pi.zero_apply, mul_one]
    change ∑ j : Fin 4, (algebraMap ℝ ℂ) (L i j) = 0
    rw [← map_sum, hL.1 i, map_zero]
  have hv : (fun _ : Fin 4 => (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congr_fun h0 0
    exact one_ne_zero this
  obtain ⟨u, hu⟩ := hUnit
  have h1 : (fun _ : Fin 4 => (1 : ℂ)) =
      ((u⁻¹ : (Matrix (Fin 4) (Fin 4) ℂ)ˣ) : Matrix (Fin 4) (Fin 4) ℂ) *ᵥ
      ((u : Matrix (Fin 4) (Fin 4) ℂ) *ᵥ (fun _ => 1)) := by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  rw [hu, hMv, mulVec_zero] at h1
  exact hv h1
