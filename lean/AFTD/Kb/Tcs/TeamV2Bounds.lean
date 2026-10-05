import AFTD.Prelude
import AFTD.Kb.Tcs.TeamVBounds
import AFTD.Kb.Tcs.TeamTau
import AFTD.Kb.Tcs.TeamTauLe
import AFTD.Kb.Tcs.TeamV2

/-!
# team_v2_bounds

Topic: algorithms   Node: c04fa99bc7e3

The scaled column potentials lie in [0, (1-2 tau)/2].
-/

lemma team_v2_bounds {m : ℕ} (j : Fin (2 * m + 3)) :
    0 ≤ team_v2 j ∧ team_v2 j ≤ (1 - 2 * team_tau m) / 2 := by
  have h1 := team_v_bounds j
  have ht := team_tau_le m
  unfold team_v2
  constructor <;> nlinarith
