import AFTD.Prelude
import AFTD.Kb.Tcs.TeamNext
import AFTD.Kb.Tcs.TeamTau
import AFTD.Kb.Tcs.TeamV2

/-!
# team_P2

Topic: algorithms   Node: 9e5fb7f9fa1d

The strengthened instance: p(i,i) = 1/2, p(i, i+1 mod n) = 1/2 - v'_i + v'_{i+1} - τ, all other entries 0.
-/

/-- The strengthened instance: `p(i,i) = 1/2`, `p(i, i+1 mod n) = 1/2 - v'_i + v'_{i+1} - τ`, all other entries `0`. -/
noncomputable def team_P2 (m : ℕ) (i j : Fin (2 * m + 3)) : ℝ :=
  if j = i then 1 / 2
  else if team_next i j then 1 / 2 - team_v2 i + team_v2 j - team_tau m else 0
