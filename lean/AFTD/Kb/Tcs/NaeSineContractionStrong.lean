import AFTD.Prelude
import AFTD.Kb.Tcs.NaeAnglePoly
import AFTD.Kb.Tcs.NaeAnglePolyNonneg
import AFTD.Kb.Tcs.NaeSinFive
import AFTD.Kb.Tcs.NaeSinSix
import AFTD.Kb.Tcs.NaeSinSmallSquare

/-!
# nae_sine_contraction_strong

Topic: quantum   Node: 61809c57ea19

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For real u with 0 ≤ u ≤ π/12, (√8/3) sin²(6u) ≤ sin(5u).
-/

theorem nae_sine_contraction_strong (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ Real.pi / 12) :
    Real.sqrt 8 / 3 * Real.sin (6 * u) ^ 2 ≤ Real.sin (5 * u) := by
  let x : ℝ := Real.sin u ^ 2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 1 / 14 := nae_sin_small_square u hu0 hu
  have hpoly := nae_angle_poly_nonneg x hx0 hx
  have hcos2 : Real.cos u ^ 2 = 1 - Real.sin u ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hcos4 : Real.cos u ^ 4 = (1 - Real.sin u ^ 2) ^ 2 := by
    calc
      Real.cos u ^ 4 = (Real.cos u ^ 2) ^ 2 := by ring
      _ = _ := by rw [hcos2]
  have hfactor : 9 * Real.sin (5 * u) ^ 2 - 8 * Real.sin (6 * u) ^ 4 =
      x * nae_angle_poly x := by
    rw [nae_sin_five, nae_sin_six]
    dsimp [x, nae_angle_poly]
    calc
      _ = 9 * Real.sin u ^ 2 * (16 * Real.sin u ^ 4 - 20 * Real.sin u ^ 2 + 5) ^ 2 -
          128 * Real.sin u ^ 4 * Real.cos u ^ 4 * (3 - 4 * Real.sin u ^ 2) ^ 4 *
            (1 - 4 * Real.sin u ^ 2) ^ 4 := by ring
      _ = _ := by rw [hcos4]; ring
  have hnonneg : 0 ≤ x * nae_angle_poly x := mul_nonneg hx0 hpoly
  have hsquared : (Real.sqrt 8 / 3 * Real.sin (6 * u) ^ 2) ^ 2 ≤ Real.sin (5 * u) ^ 2 := by
    have hsqrt : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    have hid : (Real.sqrt 8 / 3 * Real.sin (6 * u) ^ 2) ^ 2 =
        (8 / 9 : ℝ) * Real.sin (6 * u) ^ 4 := by rw [mul_pow, div_pow, hsqrt]; norm_num; ring
    rw [hid]
    nlinarith
  have hleft : 0 ≤ Real.sqrt 8 / 3 * Real.sin (6 * u) ^ 2 := by positivity
  have hright : 0 ≤ Real.sin (5 * u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  exact (sq_le_sq₀ hleft hright).mp hsquared
