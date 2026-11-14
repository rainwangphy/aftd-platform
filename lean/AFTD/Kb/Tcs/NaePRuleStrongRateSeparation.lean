import AFTD.Prelude
import AFTD.Kb.Tcs.NaePRuleStrongBaseExceedsAdversaryBase

/-!
# nae_p_rule_strong_rate_separation

Topic: quantum   Node: 7b08f507bb0f

Provenance: helper lemma. Consequence of nae_p_schedule_lower_bound_strong; related rules: arXiv:1211.0721, Section 3.3.

For every real C there is a natural d such that C(3/√2)^d is strictly less than (1/2)(12/5)^d.
-/

theorem nae_p_rule_strong_rate_separation (C : ℝ) :
    ∃ d : ℕ, C * (3 / Real.sqrt 2) ^ d < (1 / 2 : ℝ) * (12 / 5 : ℝ) ^ d := by
  let a : ℝ := 3 / Real.sqrt 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < (12 / 5 : ℝ) := nae_p_rule_strong_base_exceeds_adversary_base
  have hr : 1 < (12 / 5 : ℝ) / a := (one_lt_div ha).2 hab
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (2 * C) hr
  have hd' : 2 * C < (12 / 5 : ℝ) ^ d / a ^ d := by
    simpa [div_pow] using hd
  have ha' : 0 < a ^ d := pow_pos ha d
  have hmul := (lt_div_iff₀ ha').mp hd'
  refine ⟨d, ?_⟩
  dsimp [a] at hmul
  nlinarith
