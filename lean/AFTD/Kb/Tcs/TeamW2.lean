import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTau

/-!
# team_w2

Topic: algorithms   Node: 38f9f6b0034f

Edge probabilities of the rotation in the strengthened instance.
-/

/-- Edge probabilities of the rotation in the strengthened instance. -/
noncomputable def team_w2 {m : ℕ} (i : Fin (2 * m + 3)) : ℝ :=
  if i.val ≤ 1 then 3 / 4 - 3 / 2 * team_tau m
  else if i.val % 2 = 0 then 0 else 1 - 2 * team_tau m
