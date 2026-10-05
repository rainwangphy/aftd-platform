import AFTD.Prelude
import AFTD.Kb.Tcs.TeamT

/-!
# team_T_length

Topic: algorithms   Node: eb8e8be487a6

The alternating list 0,1,0,1,...,0 used in the first counterexample has length 2m+1.
-/

lemma team_T_length (m : ℕ) : (team_T m).length = 2 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [team_T, ih]; ring
