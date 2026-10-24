import AFTD.Prelude

/-!
# real_cubic_im_le_of_discriminant_bound

Topic: graphs   Node: e2b55bff65e6

Provenance: helper lemma. Supporting cubic algebra for standardized_laplacian_order_four_im_le (OP-465; arXiv:2610.14100 Questions 1 and 3). The two-chord family is from Section 5; experiment 4367 records its explicit factorization.

For a real monic cubic X^3-a X^2+b X-c, if a^2-3b is at least -3 and its discriminant plus 4*(a^2-3b+4)^2 is nonnegative, every complex root has imaginary part of absolute value at most one.
-/

set_option maxHeartbeats 1500000

theorem real_cubic_im_le_of_discriminant_bound
    (a b c : ℝ) (z : ℂ)
    (hz : z ^ 3 - (a : ℂ) * z ^ 2 + (b : ℂ) * z - (c : ℂ) = 0)
    (hD : -3 ≤ a ^ 2 - 3 * b)
    (hH : 0 ≤ a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 +
      18 * a * b * c + 4 * (a ^ 2 - 3 * b + 4) ^ 2) :
    |z.im| ≤ 1 := by
  let x := z.re
  let y := z.im
  have hre : x ^ 3 - 3 * x * y ^ 2 - a * (x ^ 2 - y ^ 2) + b * x - c = 0 := by
    have h := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_succ, pow_zero,
      Complex.one_re, Complex.one_im, Complex.zero_re] at h
    dsimp [x, y]
    nlinarith [h]
  have him : y * (3 * x ^ 2 - y ^ 2 - 2 * a * x + b) = 0 := by
    have h := congrArg Complex.im hz
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, Complex.zero_im] at h
    dsimp [x, y]
    nlinarith [h]
  change |y| ≤ 1
  by_contra hbad
  have hy2 : 1 < y ^ 2 := by
    have ha : 1 < |y| := lt_of_not_ge hbad
    nlinarith [sq_abs y]
  have hy : y ≠ 0 := by intro h; rw [h] at hy2; norm_num at hy2
  have hb : b = y ^ 2 - 3 * x ^ 2 + 2 * a * x := by
    have h := (mul_eq_zero.mp him).resolve_left hy
    linarith
  have hc : c = x ^ 3 - 3 * x * y ^ 2 - a * (x ^ 2 - y ^ 2) + b * x := by
    linarith [hre]
  have hfactor : a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 +
      18 * a * b * c + 4 * (a ^ 2 - 3 * b + 4) ^ 2 =
      4 * (1 - y ^ 2) * (((a - 3 * x) ^ 2 + y ^ 2 - 4) ^ 2 +
        16 * (a - 3 * x) ^ 2) := by
    rw [hc, hb]
    ring
  rw [hfactor] at hH
  let B := ((a - 3 * x) ^ 2 + y ^ 2 - 4) ^ 2 + 16 * (a - 3 * x) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBzero : B = 0 := by
    by_contra hn
    have hp : 0 < B := by exact lt_of_le_of_ne hB (Ne.symm hn)
    have hneg : 4 * (1 - y ^ 2) < 0 := by nlinarith
    have hprod := mul_neg_of_neg_of_pos hneg hp
    change 0 ≤ 4 * (1 - y ^ 2) * B at hH
    linarith
  have hsq : (a - 3 * x) ^ 2 = 0 := by
    dsimp [B] at hBzero
    nlinarith [sq_nonneg ((a - 3 * x) ^ 2 + y ^ 2 - 4)]
  rw [hb] at hD
  nlinarith [hsq]
