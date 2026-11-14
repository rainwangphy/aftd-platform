import AFTD.Prelude
import AFTD.Kb.Tcs.NaePSchedule
import AFTD.Kb.Tcs.NaePSchedulePotential
import AFTD.Kb.Tcs.NaePRuleBaseExceedsAdversaryBase

/-!
# nae_p_schedule_lower_bound

Topic: quantum   Node: 8947c01123ff

Provenance: original. Related work: arXiv:1211.0721, Section 3.3, p-computation rule analysis

Every triple (d, θ, q) reachable by the specified p-computation rule schedule with θ ≥ π/2 has scheduled query count q at least (1/2)(32/15)^d.
-/

theorem nae_p_schedule_lower_bound {d : ℕ} {θ q : ℝ} (h : nae_p_schedule d θ q)
    (hθ : Real.pi / 2 ≤ θ) :
    (1 / 2 : ℝ) * (32 / 15 : ℝ) ^ d ≤ q := by
  have hp := (nae_p_schedule_potential h).2.2.2
  have hrpos : 0 < (32 / 15 : ℝ) ^ d := by positivity
  have hmul := mul_le_mul_of_nonneg_right (le_trans hθ hp) hrpos.le
  have hcancel : (15 / 32 : ℝ) ^ d * (32 / 15 : ℝ) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  have hprod : (Real.pi * q * (15 / 32 : ℝ) ^ d) * (32 / 15 : ℝ) ^ d = Real.pi * q := by
    rw [mul_assoc, hcancel, mul_one]
  rw [hprod] at hmul
  nlinarith [Real.pi_pos]
