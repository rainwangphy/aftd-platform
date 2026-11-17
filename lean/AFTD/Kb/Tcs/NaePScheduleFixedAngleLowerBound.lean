import AFTD.Prelude
import AFTD.Kb.Tcs.NaePSchedulePotentialStrong
import AFTD.Kb.Tcs.NaePSchedule

/-!
# nae_p_schedule_fixed_angle_lower_bound

Topic: quantum   Node: 07360a98bb91

Provenance: helper lemma. The existing schedule potential bound, related to the p-computation rules in arXiv:1211.0721 Section 3.4.

If a permitted p-computation schedule at depth d reaches angle at least θ₀, then its query cost is at least (θ₀/π)(12/5)^d.
-/

/-- A fixed-angle lower bound for the restricted p-computation schedule. -/
theorem nae_p_schedule_fixed_angle_lower_bound {d : ℕ} {θ₀ θ q : ℝ} (h : nae_p_schedule d θ q)
    (hθ : θ₀ ≤ θ) :
    (θ₀ / Real.pi) * (12 / 5 : ℝ) ^ d ≤ q := by
  have hp := (nae_p_schedule_potential_strong h).2.2.2
  have hrpos : 0 < (12 / 5 : ℝ) ^ d := by positivity
  have hmul := mul_le_mul_of_nonneg_right (le_trans hθ hp) hrpos.le
  have hcancel : (5 / 12 : ℝ) ^ d * (12 / 5 : ℝ) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  have hprod : (Real.pi * q * (5 / 12 : ℝ) ^ d) * (12 / 5 : ℝ) ^ d = Real.pi * q := by
    rw [mul_assoc, hcancel, mul_one]
  rw [hprod] at hmul
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ Real.pi_pos).2
  nlinarith [Real.pi_pos]
