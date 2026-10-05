import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamIsMaxWeight
import AFTD.Kb.Tcs.TeamIsOptimal

/-!
# team_thm4_part2_exists

Topic: algorithms   Node: e42206e26463

Theorem 4 (2) of arXiv:2605.21234 under its most generous (existential) reading: some maximum-weight matching M* satisfies the bound.
-/

open Finset in
/-- Theorem 4 (2) of arXiv:2605.21234 under its most generous (existential) reading: some maximum-weight matching `M*` satisfies the bound. -/
def team_thm4_part2_exists (ε : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ n ≥ N, ∀ P : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) →
    ∀ O : Equiv.Perm (Fin n), team_isOptimal P O →
      ∃ Mstar : Equiv.Perm (Fin n), team_isMaxWeight P Mstar ∧
        ((n : ℝ) / 2 - Real.sqrt n * Real.log n ≤ team_weight P Mstar →
          team_weight P Mstar ≤ (n : ℝ) / 2 + Real.sqrt n * Real.log n →
          team_winProb P O ≤ team_winProb P Mstar
            + (4 + ε n) / ((n : ℝ) + 1) * ∑ i, (P i (Mstar i) - 1 / 2) ^ 2)
