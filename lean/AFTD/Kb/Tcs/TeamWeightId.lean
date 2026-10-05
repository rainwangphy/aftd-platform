import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamP

/-!
# team_weight_id

Topic: algorithms   Node: c051d36d5676

The identity line-up has weight n/2.
-/

/-- The identity line-up has weight `n/2`. -/
lemma team_weight_id (m : ℕ) :
    team_weight (team_P m) (1 : Equiv.Perm (Fin (2 * m + 3))) = ((2 * m + 3 : ℕ) : ℝ) / 2 := by
  unfold team_weight team_P
  simp
  ring
