import AFTD.Prelude

/-!
# team_tau

Topic: algorithms   Node: e8ea1756586d

Slack parameter τ_m = 1/(100(m+1)).
-/

/-- Slack parameter `τ_m = 1/(100(m+1))`. -/
noncomputable def team_tau (m : ℕ) : ℝ := 1 / (100 * ((m : ℝ) + 1))
