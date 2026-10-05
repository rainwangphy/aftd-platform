import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamHalfOdd
import AFTD.Kb.Tcs.TeamP

/-!
# team_id_winProb

Topic: algorithms   Node: 6ca13c0b2109

The identity line-up wins with probability exactly 1/2.
-/

/-- The identity line-up wins with probability exactly `1/2`. -/
lemma team_id_winProb (m : ℕ) : team_winProb (team_P m) 1 = 1 / 2 := by
  unfold team_winProb
  have hP : (fun i : Fin (2 * m + 3) => team_P m i ((1 : Equiv.Perm (Fin (2 * m + 3))) i))
      = fun _ => (1 / 2 : ℝ) := by
    funext i; simp [team_P]
  rw [hP, List.ofFn_const, show (2 * m + 3) / 2 + 1 = m + 2 by omega]
  exact team_half_odd m
