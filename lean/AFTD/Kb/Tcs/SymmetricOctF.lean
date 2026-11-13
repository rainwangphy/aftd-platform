import AFTD.Prelude
import AFTD.Kb.Tcs.SymmetricPowerSum

/-!
# symmetric_oct_f

Topic: algebraic_complexity   Node: 03d31d01f094

Provenance: formalization of a published result. Source: arXiv:2611.16690, Hilbert's 17th problem for symmetric functions: undecidability and a counterexample, Theorem 3.1

The degree-8 symmetric function F evaluated on an n-dimensional vector x, defined in terms of power sums by 4 p_1^2 (p_3 - 4 p_1^3)^2 + 9 p_2 (p_6 - 8 p_1^2 p_4 + 16 p_1^4 p_2) - 16 p_1^8.
-/

/-- The degree-8 symmetric function F defined in the power sum basis. -/
def symmetric_oct_f {n : ℕ} (x : Fin n → ℝ) : ℝ := 4 * (symmetric_power_sum 1 x) ^ 2 * (symmetric_power_sum 3 x - 4 * (symmetric_power_sum 1 x) ^ 3) ^ 2 + 9 * symmetric_power_sum 2 x * (symmetric_power_sum 6 x - 8 * (symmetric_power_sum 1 x) ^ 2 * symmetric_power_sum 4 x + 16 * (symmetric_power_sum 1 x) ^ 4 * symmetric_power_sum 2 x) - 16 * (symmetric_power_sum 1 x) ^ 8
