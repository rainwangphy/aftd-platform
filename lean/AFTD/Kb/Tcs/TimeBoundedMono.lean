import AFTD.Prelude
import AFTD.Kb.Tcs.TimeBounded

/-!
# time_bounded_mono

Topic: complexity_basics   Node: 678673581336

If T and T' are time bounds with T n ≤ T' n for every n, then every language decidable in time T is decidable in time T'.
-/

/-- Time-bounded decidability is monotone in the time bound. -/
theorem time_bounded_mono {Γ : Type} {T T' : ℕ → ℕ} (h : ∀ n, T n ≤ T' n) {L : Language Γ}
    (hL : TimeBounded Γ T L) : TimeBounded Γ T' L := by
  rcases hL with ⟨f, ⟨M, hM⟩, hf⟩
  exact ⟨f, ⟨M, fun n => le_trans (hM n) (h n)⟩, hf⟩
