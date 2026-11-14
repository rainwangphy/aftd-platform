import AFTD.Prelude
import AFTD.Kb.Tcs.NaePSchedule
import AFTD.Kb.Tcs.NaePRuleStrongRateSeparation
import AFTD.Kb.Tcs.NaePScheduleLowerBoundStrong

/-!
# nae_p_schedule_not_at_adversary_rate

Topic: quantum   Node: b3feb5c38686

Provenance: helper lemma. Consequence of nae_p_schedule_lower_bound_strong; related rules: arXiv:1211.0721, Section 3.3.

For every real C there is a natural d such that every real θ and q satisfying nae_p_schedule d θ q and θ ≥ π/2 has q > C(3/√2)^d.
-/

theorem nae_p_schedule_not_at_adversary_rate (C : ℝ) :
    ∃ d : ℕ, ∀ θ q : ℝ, nae_p_schedule d θ q → Real.pi / 2 ≤ θ →
      C * (3 / Real.sqrt 2) ^ d < q := by
  obtain ⟨d, hd⟩ := nae_p_rule_strong_rate_separation C
  refine ⟨d, ?_⟩
  intro θ q h hθ
  exact lt_of_lt_of_le hd (nae_p_schedule_lower_bound_strong h hθ)
