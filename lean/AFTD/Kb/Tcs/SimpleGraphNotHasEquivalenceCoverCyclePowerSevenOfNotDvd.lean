import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenCoverFourTight
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenCoverFourTightDvd
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_not_has_equivalence_cover_cycle_power_seven_of_not_dvd

Topic: combinatorics   Node: 3e20e17f40a2

Provenance: helper lemma. the lower-bound half of the k = 7 case of OP-205 (arXiv:2610.15635), research thread RT-1, case k = 7 (k + 1 = 8); SAT finds no 4-cover for 17 ≤ n ≤ 39 unless 8 | n (exp 721)

For n ≥ 22 not divisible by 8, C_n^7 cannot be covered by 4 equivalence subgraphs; this is the lower bound eq(C_n^7) ≥ 5 = m + 2 of the open case k = 7 (m = 3) of OP-205.
-/

theorem simple_graph_not_has_equivalence_cover_cycle_power_seven_of_not_dvd (n : ℕ) (hn : 22 ≤ n)
    (h8 : ¬ 8 ∣ n) : ¬ simple_graph_has_equivalence_cover (simple_graph_cycle_power n 7) 4 := by
  rintro ⟨c, hc, hcov⟩
  have : NeZero n := ⟨by omega⟩
  obtain ⟨h7, h6, h4, hspan⟩ := simple_graph_cycle_power_seven_cover_four_tight n hn c hc hcov
  exact h8 (simple_graph_cycle_power_seven_cover_four_tight_dvd n hn c hc hcov h7 h6 h4 hspan)
