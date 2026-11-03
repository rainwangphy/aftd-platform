import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedySecondMomentFormula
import AFTD.Kb.Tcs.CycleGreedyS

/-!
# cycle_greedy_second_moment_formula_eq_mean_form

Topic: online_algorithms   Node: 53f16ecda038

Provenance: formalization of a published result. Source: OP-890

For every natural number n, `cycle_greedy_second_moment_formula n = (5 * (n : ℚ) ^ 3 + (n : ℚ) ^ 2) / 48 - (n : ℚ) * ((n : ℚ) * cycle_greedy_s n / 4) / 6`.
-/

/-- Algebraic equivalence of the second moment formula to the mean representation (5n^3 + n^2)/48 - n E[C_n]/6. -/
theorem cycle_greedy_second_moment_formula_eq_mean_form (n : ℕ) :
    cycle_greedy_second_moment_formula n =
      (5 * (n : ℚ) ^ 3 + (n : ℚ) ^ 2) / 48 - (n : ℚ) * ((n : ℚ) * cycle_greedy_s n / 4) / 6 := by
  unfold cycle_greedy_second_moment_formula
  ring
