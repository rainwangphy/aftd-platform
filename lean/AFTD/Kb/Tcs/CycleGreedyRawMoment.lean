import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyMomentsAllFuel

/-!
# cycle_greedy_raw_moment

Topic: online_algorithms   Node: f8de3afe49c0

Provenance: formalization of a published result. Source: arXiv:2610.15776

The exact rational k-th raw moment of total greedy facility assignment cost on a cycle of circumference n, computed via the fuel-bounded dynamic programming moment recurrence.
-/

/-- The exact rational k-th raw moment of total greedy facility assignment cost on a cycle of circumference n. -/
def cycle_greedy_raw_moment (k : ℕ) (n : ℕ) : ℚ := (cycle_greedy_moments_all_fuel n k n (List.replicate n 1)).getD k 0
