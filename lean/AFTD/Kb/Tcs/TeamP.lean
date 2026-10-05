import AFTD.Prelude
import AFTD.Kb.Tcs.TeamW
import AFTD.Kb.Tcs.TeamNext

/-!
# team_P

Topic: algorithms   Node: a9678b2d28bd

The instance: p(i,i) = 1/2, p(i, i+1 mod n) = team_w i, all other entries 0.
-/

/-- The instance: `p(i,i) = 1/2`, `p(i, i+1 mod n) = team_w i`, all other entries `0`. -/
noncomputable def team_P (m : ℕ) (i j : Fin (2 * m + 3)) : ℝ :=
  if j = i then 1 / 2 else if team_next i j then team_w i else 0
