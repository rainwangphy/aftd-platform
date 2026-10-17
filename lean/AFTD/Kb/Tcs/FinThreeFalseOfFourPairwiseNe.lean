import AFTD.Prelude

/-!
# fin_three_false_of_four_pairwise_ne

Topic: combinatorics   Node: 22753e4193ae

Provenance: helper lemma. Helper for simple_graph_cycle_power_three_cover_three_tight_dvd (thread RT-1, the k = 3 case of OP-205, arXiv:2610.15635).

Fin 3 has no four pairwise distinct elements.
-/

theorem fin_three_false_of_four_pairwise_ne :
    ∀ w x y z : Fin 3, w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z → False := by
  intro w x y z; fin_cases w <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
