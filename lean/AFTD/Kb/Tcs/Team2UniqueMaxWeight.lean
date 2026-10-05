import AFTD.Prelude
import AFTD.Kb.Tcs.TeamIsMaxWeight
import AFTD.Kb.Tcs.TeamP2
import AFTD.Kb.Tcs.TeamWeight2Id
import AFTD.Kb.Tcs.TeamWeight2Lt

/-!
# team2_unique_maxWeight

Topic: algorithms   Node: 225e15216e3b

The identity is the unique maximum-weight matching of the strengthened instance.
-/

/-- The identity is the unique maximum-weight matching of the strengthened instance. -/
theorem team2_unique_maxWeight (m : ℕ) (M : Equiv.Perm (Fin (2 * m + 3))) :
    team_isMaxWeight (team_P2 m) M ↔ M = 1 := by
  constructor
  · intro hM
    by_contra hne
    have h1 := hM 1
    rw [team_weight2_id] at h1
    have h2 := team_weight2_lt m M hne
    linarith
  · rintro rfl σ
    rw [team_weight2_id]
    by_cases hσ : σ = 1
    · rw [hσ, team_weight2_id]
    · exact (team_weight2_lt m σ hσ).le
