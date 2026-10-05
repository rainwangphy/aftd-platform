import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail
import AFTD.Kb.Tcs.TeamT

/-!
# team_T_tail

Topic: algorithms   Node: 7f85851ae615

In the alternating list 0,1,...,0 with m ones, at least m successes happen surely and more than m never.
-/

lemma team_T_tail (m t : ℕ) : team_tail (team_T m) (t + m) = if t = 0 then 1 else 0 := by
  induction m generalizing t with
  | zero => simp [team_T, team_tail]
  | succ m ih =>
    simp only [team_T, team_tail]
    rw [show t + (m + 1) - 1 = t + m by omega, ih]
    ring
