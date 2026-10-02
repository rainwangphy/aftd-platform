import AFTD.Prelude

/-!
# catch_up_score_diff_odd_of_odd_sum

Topic: combinatorial_games   Node: dc20aa45ae65

If the sum T of player scores satisfies s_me + s_opp = T and T is odd, then the final score difference (s_me : ℤ) - (s_opp : ℤ) is an odd integer.
-/

/-- If the sum of two scores is an odd natural number, their integer difference is odd. -/
theorem catch_up_score_diff_odd_of_odd_sum {s_me s_opp T : ℕ} (h_sum : s_me + s_opp = T) (h_odd : Odd T) :
    Odd ((s_me : ℤ) - (s_opp : ℤ)) := by
  rcases h_odd with ⟨k, rfl⟩
  use (k : ℤ) - (s_opp : ℤ)
  omega
