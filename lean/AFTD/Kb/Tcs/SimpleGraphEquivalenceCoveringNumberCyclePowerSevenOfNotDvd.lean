import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverCyclePowerDyadicUpper
import AFTD.Kb.Tcs.SimpleGraphNotHasEquivalenceCoverCyclePowerSevenOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverMono
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover

/-!
# simple_graph_equivalence_covering_number_cycle_power_seven_of_not_dvd

Topic: combinatorics   Node: 554160bcb498

Provenance: original. Related work: arXiv:2610.15635, Theorems 1.3 and 1.4 (Covering powers of cycles with equivalence subgraphs); OP-205; research thread RT-1

For every n ≥ 98 not divisible by 8, the equivalence covering number of the 7th power of the n-cycle is 5 = 2 + ⌈log₂ 8⌉. This settles the case k = 7 (m = 3) of the open problem: for even n ≥ 441 not divisible by 8 the paper's Theorems 1.3-1.4 only give eq(C_n^7) ∈ {4, 5}; the larger value holds, and already from n = 98.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_seven_of_not_dvd
    (n : ℕ) (hn : 98 ≤ n) (h8 : ¬ 8 ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n 7) = 5 := by
  have hcov := simple_graph_has_equivalence_cover_cycle_power_dyadic_upper 7 3 n (by norm_num) (by norm_num)
    (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, max_le_iff]; omega)
  refine le_antisymm (Nat.sInf_le hcov) (le_csInf ⟨3 + 2, hcov⟩ fun t ht => ?_)
  by_contra hlt
  exact simple_graph_not_has_equivalence_cover_cycle_power_seven_of_not_dvd n (by omega) h8
    (simple_graph_has_equivalence_cover_mono _ (by omega) ht)
