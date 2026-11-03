import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyS

/-!
# cycle_greedy_second_moment_formula

Topic: online_algorithms   Node: 1771023411a3

Provenance: formalization of a published result. Source: OP-890

The conjectured rational closed-form second moment formula `cycle_greedy_second_moment_formula (n : ℕ) : ℚ := ((n : ℚ) ^ 2 / 48) * (5 * (n : ℚ) + 1 - 2 * cycle_greedy_s n)` for greedy online cycle assignment.
-/

/-- Conjectured closed-form formula for the exact second moment of cycle greedy assignment. -/
def cycle_greedy_second_moment_formula (n : ℕ) : ℚ := ((n : ℚ) ^ 2 / 48) * (5 * (n : ℚ) + 1 - 2 * cycle_greedy_s n)
