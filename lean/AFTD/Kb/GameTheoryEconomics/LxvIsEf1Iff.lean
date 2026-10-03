import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEf1Goods
import AFTD.Kb.GameTheoryEconomics.LxvValues
import AFTD.Kb.GameTheoryEconomics.LxvEf1
import AFTD.Kb.GameTheoryEconomics.LxvInstance
import AFTD.Kb.GameTheoryEconomics.LxvAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.LxvSumBundle
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# lxv_is_ef1_iff

Topic: fair_division   Node: 487d1f11eb26

In the instance, real EF1 is equivalent to the Boolean integer check lxv_ef1.
-/

lemma lxv_is_ef1_iff (a : Fin 6 → Fin 4) : is_ef1_goods lxv_instance a ↔ lxv_ef1 a = true := by
  simp only [is_ef1_goods, lxv_ef1, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, true_and]
  have h20 : (0 : ℝ) < 20 := by norm_num
  refine forall_congr' fun i => forall_congr' fun j => or_congr ?_ ?_
  · rw [lxv_additive_valuation, lxv_additive_valuation, lxv_sum_bundle, lxv_sum_bundle,
      div_le_div_iff_of_pos_right h20, Nat.cast_le]
  · have hmem : ∀ g, g ∈ bundle_of a j ↔ a g = j := fun g => by simp [bundle_of]
    refine exists_congr fun g => ?_
    rw [hmem]
    constructor
    · rintro ⟨hg, h⟩
      refine ⟨hg, ?_⟩
      have hs := Finset.add_sum_erase (bundle_of a j) (lxv_values i) ((hmem g).2 hg)
      rw [lxv_additive_valuation, lxv_additive_valuation, lxv_sum_bundle,
        div_le_div_iff_of_pos_right h20, Nat.cast_le] at h
      rw [lxv_sum_bundle] at hs
      omega
    · rintro ⟨hg, h⟩
      refine ⟨hg, ?_⟩
      have hs := Finset.add_sum_erase (bundle_of a j) (lxv_values i) ((hmem g).2 hg)
      rw [lxv_additive_valuation, lxv_additive_valuation, lxv_sum_bundle,
        div_le_div_iff_of_pos_right h20, Nat.cast_le]
      rw [lxv_sum_bundle] at hs
      omega
