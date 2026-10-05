import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamIsMaxWeight
import AFTD.Kb.Tcs.TeamIsOptimal

/-!
# team_thm4_part2

Topic: algorithms   Node: 0091d7cc1de5

Theorem 4 (2) of arXiv:2605.21234, with the o(1) term made explicit as a function ε: for all large n, every instance, every maximum-weight matching M* with w(M*) ∈ [n/2 - √n log n, n/2 + √n log n] and every optimal line-up O, Pr[O wins] ≤ Pr[M* wins] + (4 + ε n)/(n+1) · Σ_{e ∈ M*} (p_e - 1/2)².
-/

open Finset in
/-- Theorem 4 (2) of arXiv:2605.21234, with the `o(1)` term made explicit as a function `ε`: for all large `n`, every instance, every maximum-weight matching `M*` with `w(M*) ∈ [n/2 - √n log n, n/2 + √n log n]` and every optimal line-up `O`, `Pr[O wins] ≤ Pr[M* wins] + (4 + ε n)/(n+1) · Σ_{e ∈ M*} (p_e - 1/2)²`. -/
def team_thm4_part2 (ε : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ n ≥ N, ∀ P : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) →
    ∀ Mstar O : Equiv.Perm (Fin n), team_isMaxWeight P Mstar → team_isOptimal P O →
      (n : ℝ) / 2 - Real.sqrt n * Real.log n ≤ team_weight P Mstar →
      team_weight P Mstar ≤ (n : ℝ) / 2 + Real.sqrt n * Real.log n →
      team_winProb P O ≤ team_winProb P Mstar
        + (4 + ε n) / ((n : ℝ) + 1) * ∑ i, (P i (Mstar i) - 1 / 2) ^ 2
