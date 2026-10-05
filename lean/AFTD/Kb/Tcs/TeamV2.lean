import AFTD.Prelude
import AFTD.Kb.Tcs.TeamV
import AFTD.Kb.Tcs.TeamTau

/-!
# team_v2

Topic: algorithms   Node: f03fa39bb9d8

Scaled column potentials v'_j = (1 - 2τ) v_j (range 1/2 - τ).
-/

/-- Scaled column potentials `v'_j = (1 - 2τ) v_j` (range `1/2 - τ`). -/
noncomputable def team_v2 {m : ℕ} (j : Fin (2 * m + 3)) : ℝ := (1 - 2 * team_tau m) * team_v j
