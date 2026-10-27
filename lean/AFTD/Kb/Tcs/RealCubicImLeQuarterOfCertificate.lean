import AFTD.Prelude

/-!
# real_cubic_im_le_quarter_of_certificate

Topic: graphs   Node: 73c8d16e626c

Provenance: helper lemma. step towards standardized_laplacian_order_four_two_fractional_im_le

A complex root z of the real monic cubic z^3 + c3 z^2 + c2 z + c1 has |Im z| ≤ 1/4 provided c3^2 - 3 c2 ≥ -11/16 and 4(c3^2 c2^2 - 4 c2^3 - 4 c3^3 c1 - 27 c1^2 + 18 c1 c2 c3) + (c3^2 - 3 c2 + 1/4)^2 ≥ 0.
-/

/-- Real-cubic root bound: the D- and H-certificate on the coefficients forces |Im z| ≤ 1/4. -/
theorem real_cubic_im_le_quarter_of_certificate (c1 c2 c3 : ℝ) (z : ℂ)
    (hroot : z ^ 3 + (c3 : ℂ) * z ^ 2 + (c2 : ℂ) * z + (c1 : ℂ) = 0)
    (hD : -(11 / 16) ≤ c3 ^ 2 - 3 * c2)
    (hH : 0 ≤ 4 * (c3 ^ 2 * c2 ^ 2 - 4 * c2 ^ 3 - 4 * c3 ^ 3 * c1 - 27 * c1 ^ 2 + 18 * c1 * c2 * c3)
        + (c3 ^ 2 - 3 * c2 + 1 / 4) ^ 2) :
    |z.im| ≤ 1 / 4 := by
  set x := z.re
  set y := z.im
  have h3 : z ^ 3 = z * z * z := by ring
  have h2 : z ^ 2 = z * z := by ring
  rw [h3, h2] at hroot
  have hre_raw := congrArg Complex.re hroot
  have him_raw := congrArg Complex.im hroot
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im] at hre_raw him_raw
  have hre : x ^ 3 - 3 * x * y ^ 2 + c3 * (x ^ 2 - y ^ 2) + c2 * x + c1 = 0 := by linear_combination hre_raw
  have him : y * (3 * x ^ 2 - y ^ 2 + 2 * c3 * x + c2) = 0 := by linear_combination him_raw
  by_cases hy : y = 0
  · rw [hy, abs_zero]
    norm_num
  have hy2 : y ^ 2 = 3 * x ^ 2 + 2 * c3 * x + c2 := by
    have hmul : 3 * x ^ 2 - y ^ 2 + 2 * c3 * x + c2 = 0 := by
      cases mul_eq_zero.mp him with
      | inl h => exact (hy h).elim
      | inr h => exact h
    linear_combination -hmul
  have hc1 : c1 = (c3 + 2 * x) * (x ^ 2 + y ^ 2) := by linear_combination hre + x * hy2
  set u := (c3 + 3 * x) ^ 2
  have hu : 0 ≤ u := sq_nonneg (c3 + 3 * x)
  have hD_eq : c3 ^ 2 - 3 * c2 = u - 3 * y ^ 2 := by linear_combination 3 * hy2
  set P := 16 * u ^ 2 + 8 * (4 * y ^ 2 + 1) * u + (4 * y ^ 2 - 1) ^ 2
  have hH_eq : 4 * (c3 ^ 2 * c2 ^ 2 - 4 * c2 ^ 3 - 4 * c3 ^ 3 * c1 - 27 * c1 ^ 2 + 18 * c1 * c2 * c3)
      + (c3 ^ 2 - 3 * c2 + 1 / 4) ^ 2 = -((y ^ 2 - 1 / 16) * P) := by
    have hc2 : c2 = y ^ 2 - 3 * x ^ 2 - 2 * c3 * x := by linear_combination -hy2
    dsimp only [P, u]
    subst hc1 hc2
    ring
  rw [hH_eq] at hH
  rcases le_or_gt (y ^ 2) (1 / 16) with hle | hgt
  · have h1 : y ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      linarith [show (1 / 4 : ℝ) ^ 2 = 1 / 16 by ring]
    exact abs_le_of_sq_le_sq h1 (by norm_num)
  · have hP : P ≤ 0 := by nlinarith
    have h1 : 0 ≤ 16 * u ^ 2 := by positivity
    have h2 : 0 ≤ 8 * (4 * y ^ 2 + 1) * u := by positivity
    have h3 : 0 ≤ (4 * y ^ 2 - 1) ^ 2 := by positivity
    have hsq : (4 * y ^ 2 - 1) ^ 2 = 0 := by linarith [hP, h1, h2, h3]
    have hsq0 : 4 * y ^ 2 - 1 = 0 := sq_eq_zero_iff.mp hsq
    have hy2_val : y ^ 2 = 1 / 4 := by linarith
    have h8u : 8 * (4 * (1 / 4 : ℝ) + 1) * u ≤ 0 := by
      calc 8 * (4 * (1 / 4 : ℝ) + 1) * u
        _ = 8 * (4 * y ^ 2 + 1) * u := by rw [hy2_val]
        _ ≤ 16 * u ^ 2 + 8 * (4 * y ^ 2 + 1) * u + (4 * y ^ 2 - 1) ^ 2 := by linarith
        _ = P := rfl
        _ ≤ 0 := hP
    have hu_zero : u = 0 := by linarith
    have hD_val : c3 ^ 2 - 3 * c2 = -3 / 4 := by
      calc c3 ^ 2 - 3 * c2
        _ = u - 3 * y ^ 2 := hD_eq
        _ = 0 - 3 * (1 / 4 : ℝ) := by rw [hu_zero, hy2_val]
        _ = -3 / 4 := by ring
    linarith [hD, hD_val]
