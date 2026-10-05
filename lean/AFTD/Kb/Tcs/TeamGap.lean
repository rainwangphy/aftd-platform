import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamIsMaxWeight
import AFTD.Kb.Tcs.TeamIsOptimal
import AFTD.Kb.Tcs.TeamP
import AFTD.Kb.Tcs.TeamWeightId
import AFTD.Kb.Tcs.TeamIdMaxWeight
import AFTD.Kb.Tcs.TeamIdWinProb
import AFTD.Kb.Tcs.TeamRotWinProb

/-!
# team_gap

Topic: algorithms   Node: 6733553cbe5d

Quantitative form: on the instance of size 2m+3, the optimal line-up beats the all-1/2 maximum-weight matching by at least 1/16, while the error term of Theorem 4 (2) of arXiv:2605.21234 is 0.
-/

open Finset in
/-- Quantitative form: on the instance of size `2m+3`, the optimal line-up beats the all-`1/2` maximum-weight matching by at least `1/16`, while the error term of Theorem 4 (2) of arXiv:2605.21234 is `0`. -/
theorem team_gap (m : ℕ) (O : Equiv.Perm (Fin (2 * m + 3))) (hO : team_isOptimal (team_P m) O) :
    team_isMaxWeight (team_P m) 1 ∧
      team_weight (team_P m) 1 = ((2 * m + 3 : ℕ) : ℝ) / 2 ∧
      ∑ i : Fin (2 * m + 3), (team_P m i ((1 : Equiv.Perm (Fin (2 * m + 3))) i) - 1 / 2) ^ 2 = 0 ∧
      team_winProb (team_P m) 1 + 1 / 16 ≤ team_winProb (team_P m) O := by
  refine ⟨team_id_maxWeight m, team_weight_id m, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro i _
    simp [team_P]
  · have := hO (finRotate (2 * m + 3))
    rw [team_rot_winProb] at this
    rw [team_id_winProb]
    linarith
