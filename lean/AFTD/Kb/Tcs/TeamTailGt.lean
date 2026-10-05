import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail

/-!
# team_tail_gt

Topic: algorithms   Node: b053ececb778

The probability of more successes than there are events is 0.
-/

lemma team_tail_gt (L : List ℝ) (t : ℕ) (ht : L.length < t) : team_tail L t = 0 := by
  induction L generalizing t with
  | nil => simp [team_tail]; omega
  | cons p ps ih =>
    simp only [List.length_cons] at ht
    simp only [team_tail]
    rw [ih (t - 1) (by omega), ih t (by omega)]
    ring
