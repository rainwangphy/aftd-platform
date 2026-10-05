import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamP2

/-!
# team_weight2_id

Topic: algorithms   Node: 4044d8930695

In the strengthened instance the identity line-up has weight n/2.
-/

lemma team_weight2_id (m : ℕ) :
    team_weight (team_P2 m) (1 : Equiv.Perm (Fin (2 * m + 3))) = ((2 * m + 3 : ℕ) : ℝ) / 2 := by
  unfold team_weight team_P2
  simp
  ring
