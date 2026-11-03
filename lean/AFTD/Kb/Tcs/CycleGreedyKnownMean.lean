import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyS

/-!
# cycle_greedy_known_mean

Topic: online_algorithms   Node: 54a792beff9b

Provenance: formalization of a published result. Source: arXiv:2610.15776, Eq. (1)

The known rational expected assignment cost `cycle_greedy_known_mean (n : ℕ) : ℚ := (n : ℚ) * cycle_greedy_s n / 4` under greedy online assignment on a cycle of circumference n.
-/

/-- The known rational expected cost (n / 4) * cycle_greedy_s n for greedy online assignment on a cycle of circumference n. -/
def cycle_greedy_known_mean (n : ℕ) : ℚ := (n : ℚ) * cycle_greedy_s n / 4
