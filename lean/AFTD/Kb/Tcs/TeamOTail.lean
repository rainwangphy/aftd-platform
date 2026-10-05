import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail
import AFTD.Kb.Tcs.TeamT
import AFTD.Kb.Tcs.TeamTTail

/-!
# team_O_tail

Topic: algorithms   Node: f6d88b96fb44

With m sure wins, m+1 sure losses and two matches won with probability 3/4, winning at least m+2 matches has probability 9/16.
-/

/-- With `m` sure wins, `m+1` sure losses and two matches won with probability `3/4`, winning at least `m+2` matches has probability `9/16`. -/
lemma team_O_tail (m : ℕ) :
    team_tail ((3 / 4 : ℝ) :: (3 / 4 : ℝ) :: team_T m) (m + 2) = 9 / 16 := by
  simp only [team_tail]
  rw [show m + 2 - 1 - 1 = 0 + m by omega, show m + 2 - 1 = 1 + m by omega,
    show m + 2 = 2 + m by omega]
  rw [team_T_tail, team_T_tail, team_T_tail]
  norm_num
