import AFTD.Prelude
import AFTD.Kb.Tcs.NaePSchedule
import AFTD.Kb.Tcs.NaePScheduleNotAtAdversaryRate

/-!
# nae_p_schedule_no_uniform_adversary_rate

Topic: quantum   Node: a1ff44723332

Provenance: helper lemma. Consequence of nae_p_schedule_lower_bound_strong; related rules: arXiv:1211.0721, Section 3.3.

For any two real sequences θ and q, if for every natural d the triple (d, θ(d), q(d)) is in nae_p_schedule and θ(d) ≥ π/2, then no real C bounds q(d) by C(3/√2)^d for every natural d.
-/

theorem nae_p_schedule_no_uniform_adversary_rate
    (θ q : ℕ → ℝ)
    (h : ∀ d, nae_p_schedule d (θ d) (q d) ∧ Real.pi / 2 ≤ θ d) :
    ¬ ∃ C : ℝ, ∀ d, q d ≤ C * (3 / Real.sqrt 2) ^ d := by
  rintro ⟨C, hC⟩
  obtain ⟨d, hd⟩ := nae_p_schedule_not_at_adversary_rate C
  exact (not_lt_of_ge (hC d)) (hd (θ d) (q d) (h d).1 (h d).2)
