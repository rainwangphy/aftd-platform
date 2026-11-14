import AFTD.Prelude
import AFTD.Kb.Tcs.NaePSchedule
import AFTD.Kb.Tcs.NaePSchedulePotentialStrong
import AFTD.Kb.Tcs.NaePRuleStrongBaseExceedsAdversaryBase

/-!
# nae_p_schedule_lower_bound_strong

Topic: quantum   Node: cf9e8a3eea4f

Provenance: original. Related work: arXiv:1211.0721, Section 3.3, p-computation rule analysis

For every natural number d and real numbers θ and q, if nae_p_schedule d θ q holds and θ ≥ π/2, then q ≥ (1/2)(12/5)^d. Here nae_p_schedule is the least relation containing (0, π, 1) and closed under: composition to (d+1, arccos(1−(4/9)(1−cos θ)²), 2q); amplification to (d, arccos(cos(cθ)), cq) for positive natural c; and relaxation to (d, θ′, q) for real 0 ≤ θ′ ≤ θ. The quantity q is the budget prescribed by these operations, not a lower bound on arbitrary quantum circuits.
-/

theorem nae_p_schedule_lower_bound_strong {d : ℕ} {θ q : ℝ} (h : nae_p_schedule d θ q)
    (hθ : Real.pi / 2 ≤ θ) :
    (1 / 2 : ℝ) * (12 / 5 : ℝ) ^ d ≤ q := by
  have hp := (nae_p_schedule_potential_strong h).2.2.2
  have hrpos : 0 < (12 / 5 : ℝ) ^ d := by positivity
  have hmul := mul_le_mul_of_nonneg_right (le_trans hθ hp) hrpos.le
  have hcancel : (5 / 12 : ℝ) ^ d * (12 / 5 : ℝ) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  have hprod : (Real.pi * q * (5 / 12 : ℝ) ^ d) * (12 / 5 : ℝ) ^ d = Real.pi * q := by
    rw [mul_assoc, hcancel, mul_one]
  rw [hprod] at hmul
  nlinarith [Real.pi_pos]
