import AFTD.Prelude
import AFTD.Kb.Tcs.NaePScheduleFixedAngleLowerBound
import AFTD.Kb.Tcs.NaePRuleStrongRateSeparation
import AFTD.Kb.Tcs.NaePSchedule

/-!
# nae_p_schedule_fixed_angle_not_at_adversary_rate

Topic: quantum   Node: 8116d28e1600

Provenance: helper lemma. Consequence of the fixed-angle schedule bound and the base comparison, for the restricted p-computation rules of arXiv:1211.0721 Section 3.4.

For every positive fixed angle and every real C, some depth forces every permitted p-computation schedule attaining that angle to use more than C(3/√2)^d queries.
-/

/-- Fixed nonzero angle cannot be reached at the adversary exponential rate by the restricted p-computation schedule. -/
theorem nae_p_schedule_fixed_angle_not_at_adversary_rate (θ₀ C : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ d : ℕ, ∀ θ q : ℝ, nae_p_schedule d θ q → θ₀ ≤ θ →
      C * (3 / Real.sqrt 2) ^ d < q := by
  let s : ℝ := 2 * θ₀ / Real.pi
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨d, hd⟩ := nae_p_rule_strong_rate_separation (C / s)
  have hcs : s * (C / s) = C := by field_simp [ne_of_gt hs]
  refine ⟨d, ?_⟩
  intro θ q h hθ
  calc
    C * (3 / Real.sqrt 2) ^ d = (s * (C / s)) * (3 / Real.sqrt 2) ^ d := by rw [hcs]
    _ = s * ((C / s) * (3 / Real.sqrt 2) ^ d) := by ring
    _ < s * ((1 / 2 : ℝ) * (12 / 5 : ℝ) ^ d) := mul_lt_mul_of_pos_left hd hs
    _ = (θ₀ / Real.pi) * (12 / 5 : ℝ) ^ d := by dsimp [s]; ring
    _ ≤ q := nae_p_schedule_fixed_angle_lower_bound h hθ
