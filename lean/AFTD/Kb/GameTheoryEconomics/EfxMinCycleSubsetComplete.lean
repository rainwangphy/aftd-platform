import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleSubset
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleGoods
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitOld

/-!
# efx_min_cycle_subset_complete

Topic: fair_division   Node: 5a7f5b21932d

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

Every subset of an old triple plus good 12 has a Boolean-mask encoding.
-/

lemma efx_min_cycle_subset_complete_goods_surj (j : Fin 4) (x : Fin 13)
  (hx : x ∈ insert 12 (efx_no_self_three_split_old j)) :
  ∃ t : Fin 4, efx_min_cycle_goods j t = x := by
  fin_cases j <;> fin_cases x <;> revert hx <;> decide

theorem efx_min_cycle_subset_complete (j : Fin 4) (T : Finset (Fin 13))
  (hT : T ⊆ insert 12 (efx_no_self_three_split_old j)) :
  ∃ b : Fin 4 → Bool, efx_min_cycle_subset j b = T := by
  use fun t => decide (efx_min_cycle_goods j t ∈ T)
  ext x
  simp only [efx_min_cycle_subset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hx
    obtain ⟨t, ht⟩ := efx_min_cycle_subset_complete_goods_surj j x (hT hx)
    exact ⟨t, ht ▸ hx, ht⟩
