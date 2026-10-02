import AFTD.Prelude

/-!
# catch_up_score_diff_even_of_even_sum

Topic: combinatorial_games   Node: 4ce869534e04

If the sum T of player scores satisfies s_me + s_opp = T and T is even, then the final score difference (s_me : ℤ) - (s_opp : ℤ) is an even integer.
-/

/-- Parity invariant: if the total score is even, the score difference is an even integer. -/
theorem catch_up_score_diff_even_of_even_sum {s_me s_opp T : ℕ} (h_sum : s_me + s_opp = T) (h_even : Even T) :
    Even ((s_me : ℤ) - (s_opp : ℤ)) := by
  rcases h_even with ⟨k, rfl⟩
  use (k : ℤ) - (s_opp : ℤ)
  omega
