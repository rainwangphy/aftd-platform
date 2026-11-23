import AFTD.Prelude

/-!
# op_2178_order_two_ternary_det_sq_le

Topic: combinatorics   Node: 57f534a224a6

Provenance: formalization of a published result. Source: arXiv:2611.27591: Determinantal upper bounds for ternary matrices, Theorem 2 and Table 1

Every 2 by 2 matrix M with entries in the complex third roots of unity satisfies Complex.normSq M.det ≤ 3.
-/

lemma op_2178_order_two_ternary_det_sq_le_sub_normSq {z1 z2 : ℂ} (h1 : z1 ^ 3 = 1) (h2 : z2 ^ 3 = 1) :
    Complex.normSq (z1 - z2) ≤ 3 := by
  open Complex in
  have h_norm1 : normSq z1 = 1 := by
    have h := norm_eq_one_of_pow_eq_one h1 (by decide)
    have hsq : normSq z1 = ‖z1‖ ^ 2 := normSq_eq_norm_sq z1
    rw [hsq, h, one_pow]
  have h_norm2 : normSq z2 = 1 := by
    have h := norm_eq_one_of_pow_eq_one h2 (by decide)
    have hsq : normSq z2 = ‖z2‖ ^ 2 := normSq_eq_norm_sq z2
    rw [hsq, h, one_pow]
  let w : ℂ := z1 * starRingEnd ℂ z2
  have hw3 : w ^ 3 = 1 := by
    have h_star : (starRingEnd ℂ z2) ^ 3 = 1 := by
      have : (starRingEnd ℂ z2) ^ 3 = starRingEnd ℂ (z2 ^ 3) := (map_pow (starRingEnd ℂ) z2 3).symm
      rw [this, h2, map_one]
    calc w ^ 3 = z1 ^ 3 * (starRingEnd ℂ z2) ^ 3 := mul_pow z1 _ 3
    _ = 1 * 1 := by rw [h1, h_star]
    _ = 1 := mul_one 1
  have hw_norm : Complex.normSq w = 1 := by
    have h := Complex.norm_eq_one_of_pow_eq_one hw3 (by decide)
    have hsq : Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
    rw [hsq, h, one_pow]
  have hw_norm' : w.re ^ 2 + w.im ^ 2 = 1 := by
    rw [Complex.normSq_apply] at hw_norm
    linear_combination hw_norm
  have hw_cube_re : (w ^ 3).re = w.re ^ 3 - 3 * w.re * w.im ^ 2 := by
    let A : ℝ := w.re ^ 3 - 3 * w.re * w.im ^ 2
    let B : ℝ := 3 * w.re ^ 2 * w.im - w.im ^ 3
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    have h_cube : ((w.re : ℂ) + (w.im : ℂ) * Complex.I) ^ 3 = (A : ℂ) + (B : ℂ) * Complex.I := by
      dsimp [A, B]
      push_cast
      linear_combination (↑w.re * ↑w.im ^ 2 * 3 + ↑w.im ^ 3 * Complex.I) * hI
    have hw' : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    nth_rw 1 [hw']
    rw [h_cube]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_mul]
    rfl
  have hw_re : w.re ^ 3 - 3 * w.re * w.im ^ 2 = 1 := by
    rw [← hw_cube_re, hw3, Complex.one_re]
  have hw_poly : (w.re - 1) * (2 * w.re + 1)^2 = 0 := by
    linear_combination hw_re + 3 * w.re * hw_norm'
  have hw_cases : w.re - 1 = 0 ∨ (2 * w.re + 1)^2 = 0 := mul_eq_zero.mp hw_poly
  have hw_re_ge : - (1 : ℝ) / 2 ≤ w.re := by
    rcases hw_cases with h | h
    · linarith
    · have h' : 2 * w.re + 1 = 0 := sq_eq_zero_iff.mp h
      linarith
  rw [Complex.normSq_sub, h_norm1, h_norm2]
  show 1 + 1 - 2 * w.re ≤ 3
  linarith

/-- Every 2 by 2 matrix with entries in the complex third roots of unity has squared determinant at most 3. -/
theorem op_2178_order_two_ternary_det_sq_le
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : ∀ i j, ∃ u : rootsOfUnity 3 ℂ, ((u : ℂˣ) : ℂ) = M i j) :
    Complex.normSq M.det ≤ 3 := by
  rw [Matrix.det_fin_two]
  have h_cube (i j : Fin 2) : (M i j) ^ 3 = 1 := by
    obtain ⟨u, hu⟩ := hM i j
    rw [← hu]
    have := u.2
    rw [mem_rootsOfUnity'] at this
    exact this
  have h1 : (M 0 0 * M 1 1) ^ 3 = 1 := by
    rw [mul_pow, h_cube 0 0, h_cube 1 1, mul_one]
  have h2 : (M 0 1 * M 1 0) ^ 3 = 1 := by
    rw [mul_pow, h_cube 0 1, h_cube 1 0, mul_one]
  exact op_2178_order_two_ternary_det_sq_le_sub_normSq h1 h2
