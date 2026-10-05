import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWinProb

/-!
# team_isOptimal

Topic: algorithms   Node: 8c05e9c0b5d9

π is an optimal line-up (maximises the winning probability).
-/

/-- `π` is an optimal line-up (maximises the winning probability). -/
def team_isOptimal {n : ℕ} (P : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), team_winProb P σ ≤ team_winProb P π
