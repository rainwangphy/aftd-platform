import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail

/-!
# team_tail_zero

Topic: algorithms   Node: bf87e8582a83

The probability of at least 0 successes is 1.
-/

lemma team_tail_zero (L : List ℝ) : team_tail L 0 = 1 := by
  induction L with
  | nil => simp [team_tail]
  | cons p ps ih => simp [team_tail, ih]
