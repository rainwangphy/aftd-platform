import AFTD.Prelude
import AFTD.Kb.Tcs.TeamV2
import AFTD.Kb.Tcs.TeamP2

/-!
# team_dual2_diag

Topic: algorithms   Node: 841b75d36534

In the strengthened instance the dual constraint is tight on the diagonal: p(i,i) = u_i + v_i.
-/

lemma team_dual2_diag (m : ℕ) (i : Fin (2 * m + 3)) :
    team_P2 m i i = (1 / 2 - team_v2 i) + team_v2 i := by
  simp [team_P2]
