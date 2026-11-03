import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyMomentsFuel

/-!
# cycle_greedy_moments

Topic: online_algorithms   Node: a752401b2572

Provenance: formalization of a published result. Source: arXiv:2610.15776, Corollary 18

The function `cycle_greedy_moments (n : ℕ) (g : List ℕ) : ℚ × ℚ` defined as `cycle_greedy_moments_fuel g.length n g`.
-/

/-- Computes first and second moments of remaining greedy assignment cost from gap configuration g on an n-cycle. -/
def cycle_greedy_moments (n : ℕ) (g : List ℕ) : ℚ × ℚ := cycle_greedy_moments_fuel g.length n g
