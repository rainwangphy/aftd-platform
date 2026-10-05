import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight

/-!
# team_isMaxWeight

Topic: algorithms   Node: 7a5e3e063829

π is a maximum-weight perfect matching.
-/

/-- `π` is a maximum-weight perfect matching. -/
def team_isMaxWeight {n : ℕ} (P : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), team_weight P σ ≤ team_weight P π
