import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverMono
import AFTD.Kb.Tcs.SimpleGraphNotHasEquivalenceCoverCyclePowerThreeOfNotDvd

/-!
# simple_graph_equivalence_covering_number_cycle_power_forty_six_three

Topic: combinatorics   Node: 6b0f762d85fe

Provenance: original. Related work: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs): the smallest instance (k = 3, n = 46) of the case Theorems 1.3 and 1.4 do not cover; Theorem 1.4 does not apply below n = 164, so only 3 ≤ eq ≤ 5 is known. SAT search: experiment 708.

eq(C_46^3) = 4: the smallest case of the open problem (k = 3, n = 46 even, 4 ∤ 46, 46 ≥ 45), where the paper only knows eq ∈ {3, 4, 5}.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_forty_six_three :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power 46 3) = 4 := by
  have hcov : simple_graph_has_equivalence_cover (simple_graph_cycle_power 46 3) 4 := by
    refine ⟨fun s u => ((([[0, 0, 2, 2, 4, 4, 4, 4, 8, 8, 8, 8, 12, 12, 12, 12, 16, 16, 16, 16, 20, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 32, 32, 32, 32, 36, 36, 36, 36, 40, 40, 40, 40, 0, 0],
      [0, 1, 2, 3, 1, 5, 3, 7, 5, 9, 7, 11, 9, 13, 11, 15, 13, 17, 15, 19, 17, 21, 19, 23, 21, 25, 23, 27, 25, 29, 27, 31, 29, 33, 31, 35, 33, 37, 35, 39, 37, 41, 39, 0, 41, 2],
      [0, 0, 0, 0, 4, 4, 6, 6, 6, 6, 10, 10, 10, 10, 14, 14, 14, 14, 18, 18, 18, 18, 22, 22, 22, 22, 26, 26, 26, 26, 30, 30, 30, 30, 34, 34, 34, 34, 38, 38, 38, 38, 42, 42, 42, 42],
      [0, 0, 2, 2, 2, 2, 6, 6, 6, 6, 10, 10, 10, 10, 14, 14, 14, 14, 18, 18, 18, 18, 22, 22, 22, 22, 26, 26, 26, 26, 30, 30, 30, 30, 34, 34, 34, 34, 38, 38, 38, 38, 42, 42, 42, 42]]
      : List (List ℕ)).getD s.val []).getD u.val 0 : ZMod 46), ?_, ?_⟩
    · show ∀ (s : Fin 4) (u v : ZMod 46), u ≠ v → _ = _ → u ≠ v ∧ min (u - v).val (v - u).val ≤ 3
      decide +kernel
    · show ∀ (u v : ZMod 46), u ≠ v ∧ min (u - v).val (v - u).val ≤ 3 → ∃ s : Fin 4, _
      decide +kernel
  refine le_antisymm (Nat.sInf_le hcov) (le_csInf ⟨4, hcov⟩ fun t ht => ?_)
  by_contra hlt
  exact simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd 46 (by norm_num)
    (by norm_num) (simple_graph_has_equivalence_cover_mono _ (by omega) ht)
