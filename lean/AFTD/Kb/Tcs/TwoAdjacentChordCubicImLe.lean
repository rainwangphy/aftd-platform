import AFTD.Prelude
import AFTD.Kb.Tcs.RealCubicImLeOfDiscriminantBound

/-!
# two_adjacent_chord_cubic_im_le

Topic: graphs   Node: 794a96a42bff

Provenance: helper lemma. Supporting cubic algebra for standardized_laplacian_order_four_im_le (OP-465; arXiv:2610.14100 Questions 1 and 3). The two-chord family is from Section 5; experiment 4367 records its explicit factorization.

Every complex root of the nonzero cubic factor of the unscaled directed four-cycle with adjacent chord weights t,u has imaginary part of absolute value at most one, for arbitrary real chord weights.
-/

set_option maxHeartbeats 1500000

theorem two_adjacent_chord_cubic_im_le (t u : ℝ) (z : ℂ)
    (hz : z ^ 3 - ((t + u + 4 : ℝ) : ℂ) * z ^ 2 +
      ((t * u + 3 * t + 3 * u + 6 : ℝ) : ℂ) * z -
      ((2 * t * u + 2 * t + 2 * u + 4 : ℝ) : ℂ) = 0) :
    |z.im| ≤ 1 := by
  apply real_cubic_im_le_of_discriminant_bound
    (t + u + 4) (t * u + 3 * t + 3 * u + 6)
    (2 * t * u + 2 * t + 2 * u + 4) z hz
  · nlinarith [sq_nonneg (1 - t), sq_nonneg (1 - u), sq_nonneg (t - u)]
  · have hfactor :
        (t + u + 4) ^ 2 * (t * u + 3 * t + 3 * u + 6) ^ 2 -
        4 * (t * u + 3 * t + 3 * u + 6) ^ 3 -
        4 * (t + u + 4) ^ 3 * (2 * t * u + 2 * t + 2 * u + 4) -
        27 * (2 * t * u + 2 * t + 2 * u + 4) ^ 2 +
        18 * (t + u + 4) * (t * u + 3 * t + 3 * u + 6) *
          (2 * t * u + 2 * t + 2 * u + 4) +
        4 * ((t + u + 4) ^ 2 - 3 * (t * u + 3 * t + 3 * u + 6) + 4) ^ 2 =
        (t - u) ^ 2 * ((1 - t) ^ 2 * (1 - u) ^ 2 +
          3 * (1 - t) ^ 2 + 3 * (1 - u) ^ 2 + ((1 - t) + (1 - u)) ^ 2 + 9) := by
      ring
    rw [hfactor]
    positivity
