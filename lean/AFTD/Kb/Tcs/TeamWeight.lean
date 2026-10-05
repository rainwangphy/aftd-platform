import AFTD.Prelude

/-!
# team_weight

Topic: algorithms   Node: dc684523aa4c

A line-up of team 1 against the fixed line-up of team 2 is a perfect matching, i.e. a permutation π of the n positions (player i of team 1 meets player π i of team 2). Its weight is the expected number of wins Σ_i p(i, π i) (arXiv:2605.21234, Section 6).
-/

open Finset in
/-- A line-up of team 1 against the fixed line-up of team 2 is a perfect matching, i.e. a permutation `π` of the `n` positions (player `i` of team 1 meets player `π i` of team 2). Its weight is the expected number of wins `Σ_i p(i, π i)` (arXiv:2605.21234, Section 6). -/
noncomputable def team_weight {n : ℕ} (P : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, P i (π i)
