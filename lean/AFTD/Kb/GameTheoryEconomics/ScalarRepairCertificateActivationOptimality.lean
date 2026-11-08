import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ScalarRepairCertificate

/-!
# scalar_repair_certificate_activation_optimality

Topic: equilibria   Node: 5f12f2025b0c

Provenance: formalization of a published result. Source: arXiv:2611.06076:2505

For all real numbers f, f_star, s_star, and sigma_star satisfying s_star = 1 - f_star, sigma_star = 9 - 16 * f_star + 6 * f_star², 2 * f_star³ - 4 * f_star² + 1 = 0, f ≠ 0, and f + s_star ≠ 0, the scalar repair certificate satisfies sigma_star - scalar_repair_certificate f s_star = sigma_star * (f - f_star)² / (f * (f + s_star)).
-/

/-- Optimality of f_star across activation parameters at the worst-case memory s_star. -/
theorem scalar_repair_certificate_activation_optimality (f f_star s_star sigma_star : ℝ)
    (hs : s_star = 1 - f_star)
    (hsigma : sigma_star = 9 - 16 * f_star + 6 * f_star^2)
    (hcubic : 2 * f_star^3 - 4 * f_star^2 + 1 = 0)
    (hf_pos : f ≠ 0)
    (hdenom : f + s_star ≠ 0) :
    sigma_star - scalar_repair_certificate f s_star =
    sigma_star * (f - f_star)^2 / (f * (f + s_star)) := by
  have hd : f * (f + s_star) ≠ 0 := mul_ne_zero hf_pos hdenom
  unfold scalar_repair_certificate
  have hpoly : sigma_star * (f * (f + s_star)) - (1 + s_star) * (f + (2 * f - 1) * s_star) =
      sigma_star * (f - f_star)^2 := by
    subst hs hsigma
    linear_combination (3 * f - 3 * f_star + 2) * hcubic
  have h1 : sigma_star * (f * (f + s_star)) =
      sigma_star * (f - f_star)^2 + (1 + s_star) * (f + (2 * f - 1) * s_star) := by
    linear_combination hpoly
  rw [← eq_div_iff hd] at h1
  rw [add_div] at h1
  linarith
