import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamOTail
import AFTD.Kb.Tcs.TeamP
import AFTD.Kb.Tcs.TeamRotList

/-!
# team_rot_winProb

Topic: algorithms   Node: b5ca440d0f10

The rotation line-up wins with probability 9/16.
-/

/-- The rotation line-up wins with probability `9/16`. -/
lemma team_rot_winProb (m : ℕ) :
    team_winProb (team_P m) (finRotate (2 * m + 3)) = 9 / 16 := by
  unfold team_winProb
  rw [team_rot_list, show (2 * m + 3) / 2 + 1 = m + 2 by omega]
  exact team_O_tail m
