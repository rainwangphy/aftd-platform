import AFTD.Prelude
import AFTD.Kb.Physics.ChebyshevSemicircleSlowModeLimit

/-!
# chebyshev_semicircle_slow_mode_limit_zero

Topic: statistical_mechanics   Node: 7b79bd2f65a7

Provenance: helper lemma. arXiv:2609.13387

At rescaled time t = 0, the Chebyshev-semicircle limiting profile equals 1 for every integer m >= 2.
-/

lemma chebyshev_semicircle_slow_mode_limit_zero_integral_sqrt_four_sub_sq :
    ∫ x in (-2 : ℝ)..2, Real.sqrt (4 - x ^ 2) = 2 * Real.pi := by
  have hcomp := @intervalIntegral.mul_integral_comp_mul_left (-1) 1 (fun x => Real.sqrt (4 - x ^ 2)) 2
  norm_num at hcomp
  rw [← hcomp]
  have hsimp : (fun x => Real.sqrt (4 - (2 * x) ^ 2)) = (fun x => 2 * Real.sqrt (1 - x ^ 2)) := by
    ext x
    have h1 : 4 - (2 * x) ^ 2 = 4 * (1 - x ^ 2) := by ring
    rw [h1, Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hsimp]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_sqrt_one_sub_sq]
  ring

/-- At rescaled time t = 0, the Chebyshev-semicircle limiting profile equals 1. -/
theorem chebyshev_semicircle_slow_mode_limit_zero (m : ℕ) (hm : 2 ≤ m) :
    chebyshev_semicircle_slow_mode_limit m 0 = 1 := by
  unfold chebyshev_semicircle_slow_mode_limit
  have h_int : (fun x : ℝ => Complex.exp (Complex.I * ((0 : ℝ) * (Polynomial.Chebyshev.U ℝ (m - 1)).eval (x / 2) : ℂ)) *
      ((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ)) =
      (fun x : ℝ => (((Real.sqrt (4 - x ^ 2) / (2 * Real.pi) : ℝ) : ℂ))) := by
    ext x
    simp
  rw [h_int]
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_div]
  rw [chebyshev_semicircle_slow_mode_limit_zero_integral_sqrt_four_sub_sq]
  have hpi : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  rw [div_self hpi]
  simp
