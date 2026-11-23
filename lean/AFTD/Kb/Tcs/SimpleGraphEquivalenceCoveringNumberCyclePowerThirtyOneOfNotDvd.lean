import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfAlternatingPaired
import AFTD.Kb.Tcs.CyclePowerFifteenModelNoIsland
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDyadicOfClassShape
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerThirtyOneOfAlternating
import AFTD.Kb.Tcs.CyclePowerThirtyOneModelAlternating

/-!
# simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_not_dvd

Topic: combinatorics   Node: 426af50a3808

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Case k = 31 (m = 5).

For every even n ≥ 31713 = 31²·33 not divisible by 32, the equivalence covering number of the 31st power of the n-cycle is 7 = 2 + log₂ 32: the k = 31 (m = 5) case of OP-205.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_not_dvd
    (n : ℕ) (hn : 31713 ≤ n) (hev : Even n) (hnd : ¬ 32 ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n 31) = 7 := simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_alternating
  cycle_power_thirty_one_model_alternating n hn hev hnd
