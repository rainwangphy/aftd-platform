import AFTD.Prelude
import AFTD.Kb.Tcs.TeamT2

/-!
# team_T2_length

Topic: algorithms   Node: f8b333bbf2cf

The list 0,b,0,b,...,0 with m copies of b has length 2m+1.
-/

lemma team_T2_length (b : ℝ) (m : ℕ) : (team_T2 b m).length = 2 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [team_T2, ih]; ring
