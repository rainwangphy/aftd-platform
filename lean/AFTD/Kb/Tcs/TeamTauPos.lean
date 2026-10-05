import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTau

/-!
# team_tau_pos

Topic: algorithms   Node: 47903a1a7e31

The slack tau = 1/(100(m+1)) is positive.
-/

lemma team_tau_pos (m : ℕ) : 0 < team_tau m := by
  unfold team_tau; positivity
