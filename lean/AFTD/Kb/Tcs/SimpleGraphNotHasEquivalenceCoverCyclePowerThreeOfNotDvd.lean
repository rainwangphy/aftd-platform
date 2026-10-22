import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeCoverThreeTight
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeCoverThreeTightDvd

/-!
# simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd

Topic: combinatorics   Node: 3266acfef1d9

Provenance: original. Related work: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs): Theorem 3.4 gives eq(C_n^k) ≥ 2 + ⌈log₂(k+1)⌉ only for odd n when k + 1 is a power of two; the case n ≡ 2 (mod 4), k = 3 is the smallest instance the paper's theorems do not cover. Transfer-matrix computation: experiment 712.

For every n ≥ 10 not divisible by 4, the cube C_n^3 of the n-cycle cannot be covered by 3 equivalence subgraphs; with the lower bound eq ≥ 3 this gives eq(C_n^3) ≥ 4 = 2 + ⌈log₂ 4⌉, the k = 3 case of the lower bound in the open problem (and of Theorem 3.4 for odd n), for all even n ≡ 2 (mod 4) as well.
-/

theorem simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd (n : ℕ) (hn : 10 ≤ n)
    (h4 : ¬ 4 ∣ n) : ¬ simple_graph_has_equivalence_cover (simple_graph_cycle_power n 3) 3 := by
  rintro ⟨c, hc, hcov⟩
  have : NeZero n := ⟨by omega⟩
  obtain ⟨h3, h2, hspan⟩ := simple_graph_cycle_power_three_cover_three_tight n hn c hc hcov
  exact h4 (simple_graph_cycle_power_three_cover_three_tight_dvd n hn c hc h3 h2 hspan)
