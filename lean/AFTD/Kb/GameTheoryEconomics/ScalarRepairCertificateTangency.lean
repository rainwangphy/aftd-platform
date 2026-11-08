import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ScalarRepairCertificate

/-!
# scalar_repair_certificate_tangency

Topic: equilibria   Node: cddd3a67f4bb

Provenance: formalization of a published result. Source: arXiv:2611.06076:2499

For all real numbers f_star, s_star, sigma_star, and H satisfying s_star = 1 - f_star, sigma_star = 9 - 16 * f_star + 6 * f_star², 2 * f_star³ - 4 * f_star² + 1 = 0, f_star ≠ 0, and f_star + H ≠ 0, the scalar repair certificate satisfies scalar_repair_certificate f_star H - sigma_star = (2 * f_star - 1) * (H - s_star)² / (f_star * (f_star + H)).
-/

/-- Quadratic tangency of the scalar repair certificate at the critical point s_star. -/
theorem scalar_repair_certificate_tangency (f_star s_star sigma_star H : ℝ)
    (hs : s_star = 1 - f_star)
    (hsigma : sigma_star = 9 - 16 * f_star + 6 * f_star^2)
    (hcubic : 2 * f_star^3 - 4 * f_star^2 + 1 = 0)
    (hf_pos : f_star ≠ 0)
    (hdenom : f_star + H ≠ 0) :
    scalar_repair_certificate f_star H - sigma_star =
    (2 * f_star - 1) * (H - s_star)^2 / (f_star * (f_star + H)) := by
  unfold scalar_repair_certificate
  rw [hs, hsigma]
  have hD : f_star * (f_star + H) ≠ 0 := mul_ne_zero hf_pos hdenom
  apply mul_right_cancel₀ hD
  calc
    ((1 + H) * (f_star + (2 * f_star - 1) * H) / (f_star * (f_star + H)) - (9 - 16 * f_star + 6 * f_star ^ 2)) *
        (f_star * (f_star + H))
      = (1 + H) * (f_star + (2 * f_star - 1) * H) - (9 - 16 * f_star + 6 * f_star ^ 2) * (f_star * (f_star + H)) := by
        rw [sub_mul, div_mul_cancel₀ _ hD]
    _ = (2 * f_star - 1) * (H - (1 - f_star)) ^ 2 := by
        linear_combination (1 - 3 * f_star - 3 * H) * hcubic
    _ = (2 * f_star - 1) * (H - (1 - f_star)) ^ 2 / (f_star * (f_star + H)) * (f_star * (f_star + H)) := by
        rw [div_mul_cancel₀ _ hD]
