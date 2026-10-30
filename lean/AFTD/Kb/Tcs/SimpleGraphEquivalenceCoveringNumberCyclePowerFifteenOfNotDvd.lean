import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenModelNoIsland
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDyadicOfClassShape
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# simple_graph_equivalence_covering_number_cycle_power_fifteen_of_not_dvd

Topic: combinatorics   Node: 3a1bc3d20908

Provenance: original. Related work: arXiv:2610.15635, Theorems 1.3 and 1.4 (Covering powers of cycles with equivalence subgraphs); OP-205; research thread RT-1

For every even n ≥ 3825 = 15²·17 not divisible by 16, the equivalence covering number of the 15th power of the n-cycle is 6 = 2 + ⌈log₂ 16⌉. This settles the case k = 15 (m = 4) of the open problem: the paper's Theorems 1.3-1.4 leave eq(C_n^15) ∈ {5, 6} open for these n; the larger value holds.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_fifteen_of_not_dvd
    (n : ℕ) (hn : 3825 ≤ n) (hev : Even n) (hnd : ¬ 16 ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n 15) = 6 :=
  simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape 15 4 n (by norm_num) (by norm_num)
    (by simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, max_le_iff]; omega) hev (by simpa using hnd)
    (fun x h1 h2 h3 h4 => cycle_power_fifteen_model_no_island x h1 h2 h3 h4)
