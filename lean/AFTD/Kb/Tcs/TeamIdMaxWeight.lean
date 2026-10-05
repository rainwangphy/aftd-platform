import AFTD.Prelude
import AFTD.Kb.Tcs.TeamIsMaxWeight
import AFTD.Kb.Tcs.TeamP
import AFTD.Kb.Tcs.TeamWeightLe
import AFTD.Kb.Tcs.TeamWeightId

/-!
# team_id_maxWeight

Topic: algorithms   Node: 6a9686d9d5fe

The identity line-up (all edges 1/2) is a maximum-weight matching.
-/

/-- The identity line-up (all edges `1/2`) is a maximum-weight matching. -/
lemma team_id_maxWeight (m : ℕ) : team_isMaxWeight (team_P m) 1 := by
  intro σ
  rw [team_weight_id]
  exact team_weight_le m σ
