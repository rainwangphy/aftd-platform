import AFTD.Prelude

/-!
# team_wins

Topic: algorithms   Node: 39f10b67699d

Number of successes in an outcome vector.
-/

open Finset in
/-- Number of successes in an outcome vector. -/
def team_wins {n : ℕ} (ω : Fin n → Bool) : ℕ := ∑ i, if ω i = true then 1 else 0
