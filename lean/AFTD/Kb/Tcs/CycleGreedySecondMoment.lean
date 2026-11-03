import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyMoments

/-!
# cycle_greedy_second_moment

Topic: online_algorithms   Node: 1a5333958a53

Provenance: formalization of a published result. Source: arXiv:2610.15776 and OP-890

The rational exact second moment `cycle_greedy_second_moment (n : ℕ) : ℚ := (cycle_greedy_moments n (List.replicate n 1)).2` of total greedy assignment cost on a cycle of circumference n.
-/

/-- Exact second moment of the total greedy assignment cost on a cycle of circumference n. -/
def cycle_greedy_second_moment (n : ℕ) : ℚ := (cycle_greedy_moments n (List.replicate n 1)).2
