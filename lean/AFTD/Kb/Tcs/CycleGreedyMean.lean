import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyMoments

/-!
# cycle_greedy_mean

Topic: online_algorithms   Node: 49ba82b1ff58

Provenance: formalization of a published result. Source: arXiv:2610.15776, Section 3 and Theorem 9

The rational expected assignment cost `cycle_greedy_mean (n : ℕ) : ℚ := (cycle_greedy_moments n (List.replicate n 1)).1` under greedy online assignment on a cycle of circumference n.
-/

/-- Expected total assignment cost of the greedy online algorithm on a cycle of circumference n. -/
def cycle_greedy_mean (n : ℕ) : ℚ := (cycle_greedy_moments n (List.replicate n 1)).1
