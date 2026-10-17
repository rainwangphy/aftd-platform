import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverCyclePowerThreeOfModFourEqTwo
import AFTD.Kb.Tcs.SimpleGraphNotHasEquivalenceCoverCyclePowerThreeOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverMono
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_equivalence_covering_number_cycle_power_three_of_mod_four_eq_two

Topic: combinatorics   Node: 36678d282ef4

Provenance: original. Related work: OP-205 (arXiv:2610.15635): the case k + 1 = 2^m, n even, (k + 1) ∤ n is left open; this is its case k = 3.

For every n ≥ 10 with n ≡ 2 (mod 4), eq(C_n^3) = 4 = 2 + ⌈log₂ 4⌉. This settles the case k = 3 (m = 2) of the open problem: for even n ≥ 45 not divisible by 4 the paper only knows eq(C_n^3) ∈ {3, 4}; the larger value holds, and already from n = 10.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_three_of_mod_four_eq_two (n : ℕ) (hn : 10 ≤ n) (h4 : n % 4 = 2) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n 3) = 4 := by
  have hcov := simple_graph_has_equivalence_cover_cycle_power_three_of_mod_four_eq_two n hn h4
  refine le_antisymm (Nat.sInf_le hcov) (le_csInf ⟨4, hcov⟩ fun t ht => ?_)
  by_contra hlt
  exact simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd n hn (by omega)
    (simple_graph_has_equivalence_cover_mono _ (by omega) ht)
