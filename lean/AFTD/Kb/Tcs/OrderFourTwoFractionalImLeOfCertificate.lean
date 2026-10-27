import AFTD.Prelude
import AFTD.Kb.Tcs.RealCubicImLeQuarterOfCertificate
import AFTD.Kb.Tcs.StandardizedLaplacianOrderFourZeroMemSpectrum
import AFTD.Kb.Tcs.IsStandardizedLaplacianTwoFractional
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# order_four_two_fractional_im_le_of_certificate

Topic: graphs   Node: a69f61fc5ea4

Provenance: helper lemma. step towards standardized_laplacian_order_four_two_fractional_im_le

If the coefficients c1, c2, c3 of the characteristic polynomial of an order-4 two-fractional standardized Laplacian satisfy the D- and H-certificate, then every z in the complexified spectrum has |Im z| ≤ 1/4.
-/

/-- Assembly: the coefficient certificate on L.charpoly plus z in the spectrum gives |Im z| ≤ 1/4. -/
theorem order_four_two_fractional_im_le_of_certificate (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian_two_fractional 4 L) (z : ℂ)
    (hz : z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)))
    (hcert : let c1 := (L.charpoly).coeff 1
             let c2 := (L.charpoly).coeff 2
             let c3 := (L.charpoly).coeff 3
             (-(11 / 16 : ℝ) ≤ c3 ^ 2 - 3 * c2) ∧
               (0 ≤ 4 * (c3 ^ 2 * c2 ^ 2 - 4 * c2 ^ 3 - 4 * c3 ^ 3 * c1 - 27 * c1 ^ 2 + 18 * c1 * c2 * c3)
                 + (c3 ^ 2 - 3 * c2 + 1 / 4) ^ 2)) :
    |z.im| ≤ 1 / 4 := by
  dsimp only at hcert
  obtain ⟨hD, hH⟩ := hcert
  set c1 := (L.charpoly).coeff 1
  set c2 := (L.charpoly).coeff 2
  set c3 := (L.charpoly).coeff 3
  have hc0 : (L.charpoly).coeff 0 = 0 := by
    have h0 : (0 : ℂ) ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)) :=
      standardized_laplacian_order_four_zero_mem_spectrum L hL.1
    have h1 : ((L.map (algebraMap ℝ ℂ)).charpoly).IsRoot 0 :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mp h0
    have h2 : ((L.map (algebraMap ℝ ℂ)).charpoly).coeff 0 = 0 :=
      Polynomial.zero_isRoot_iff_coeff_zero_eq_zero.mp h1
    rw [Matrix.charpoly_map, Polynomial.coeff_map] at h2
    exact (algebraMap ℝ ℂ).injective (by simpa using h2)
  have hd : L.charpoly.natDegree = 4 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hm : L.charpoly.coeff 4 = 1 := by
    have h := (Matrix.charpoly_monic L).coeff_natDegree
    rwa [hd] at h
  have hpoly : L.charpoly = Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X := by
    ext n
    rcases n with _ | _ | _ | _ | _ | n
    · simp [hc0]
    · simp [c1]
    · simp [c2]
    · simp [c3]
    · simp [hm]
    · have h1 : L.charpoly.coeff (n + 5) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
      have h2 : (Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X : Polynomial ℝ).coeff (n + 5) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have : (Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X : Polynomial ℝ).natDegree ≤ 4 := by
          compute_degree!
        omega
      rw [h1, h2]
  have hroot : ((L.map (algebraMap ℝ ℂ)).charpoly).IsRoot z :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
  rw [Matrix.charpoly_map, hpoly] at hroot
  dsimp [Polynomial.IsRoot] at hroot
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hroot
  have hfactor : z * (z ^ 3 + (c3 : ℂ) * z ^ 2 + (c2 : ℂ) * z + (c1 : ℂ)) = 0 := by
    linear_combination hroot
  rcases mul_eq_zero.mp hfactor with hz0 | hcubic
  · subst hz0
    simp
  · exact real_cubic_im_le_quarter_of_certificate c1 c2 c3 z hcubic hD hH
