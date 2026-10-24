import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCakeAllocation
import AFTD.Kb.GameTheoryEconomics.IsEqualLengthAllocation
import AFTD.Kb.GameTheoryEconomics.IsPropLbProportional
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# equal_length_proportional_cake_prefix_volume

Topic: fair_division   Node: 387783a4f6e0

Provenance: helper lemma. scout/2610-19733-exact-cut-complexity-of-equal-length-proportional-cake-cutt.md:385

In any equal-length proportional cake allocation C : Fin n → Set ℝ for n ≥ 1 under the identical valuation profile where each agent values only the prefix [0, 1/n], each bundle C i has prefix Lebesgue measure volume (C i ∩ Set.Icc 0 (1 / n)) equal to ENNReal.ofReal (1 / n^2).
-/

/-- In any equal-length proportional allocation under the lower-bound valuation profile, each bundle has prefix volume 1/n^2. -/
theorem equal_length_proportional_cake_prefix_volume (n : ℕ) (hn : 1 ≤ n)
    (C : Fin n → Set ℝ)
    (h_alloc : is_cake_allocation n C)
    (h_len : is_equal_length_allocation n C)
    (h_prop : is_prop_lb_proportional n C)
    (i : Fin n) :
    MeasureTheory.volume (C i ∩ Set.Icc 0 (1 / (n : ℝ))) = ENNReal.ofReal (1 / ((n : ℝ) ^ 2)) := by
  have _ := h_len
  have h_eq_of_sum_eq (k : Fin n) (f g : Fin n → ENNReal)
      (h_le : ∀ j, g j ≤ f j)
      (h_sum : ∑ j, f j = ∑ j, g j)
      (h_top : (∑ j, g j) ≠ ⊤) :
      f k = g k := by
    by_contra h_ne
    have h_lt : g k < f k := lt_of_le_of_ne (h_le k) (Ne.symm h_ne)
    have h_split_f : ∑ j, f j = f k + ∑ j ∈ Finset.univ.erase k, f j :=
      (Finset.add_sum_erase Finset.univ f (Finset.mem_univ k)).symm
    have h_split_g : ∑ j, g j = g k + ∑ j ∈ Finset.univ.erase k, g j :=
      (Finset.add_sum_erase Finset.univ g (Finset.mem_univ k)).symm
    have h_rest_le : ∑ j ∈ Finset.univ.erase k, g j ≤ ∑ j ∈ Finset.univ.erase k, f j :=
      Finset.sum_le_sum (fun j _ => h_le j)
    have h_rest_ne_top : (∑ j ∈ Finset.univ.erase k, g j) ≠ ⊤ := by
      apply ne_of_lt
      exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) (lt_top_iff_ne_top.mpr h_top)
    have h_strict : ∑ j, g j < ∑ j, f j := by
      rw [h_split_g, h_split_f]
      exact ENNReal.add_lt_add_of_lt_of_le h_rest_ne_top h_lt h_rest_le
    exact (ne_of_lt h_strict) h_sum.symm
  have hn_ne_zero : (n : ENNReal) ≠ 0 := by
    norm_cast
    omega
  have hn_ne_top : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have h_le : ∀ j, (1 : ENNReal) / ((n : ENNReal) ^ 2) ≤ MeasureTheory.volume (C j ∩ Set.Icc 0 (1 / (n : ℝ))) := by
    intro j
    have hj := h_prop j
    have h1 := (ENNReal.div_le_iff' hn_ne_zero hn_ne_top).mpr hj
    rw [sq, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hn_ne_zero) (Or.inl hn_ne_top),
        ← mul_assoc, ← div_eq_mul_inv, ← div_eq_mul_inv]
    exact h1
  have h_sum_g : ∑ _j : Fin n, (1 : ENNReal) / ((n : ENNReal) ^ 2) = 1 / (n : ENNReal) := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [sq, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hn_ne_zero) (Or.inl hn_ne_top)]
    rw [one_mul, ← mul_assoc, ENNReal.mul_inv_cancel hn_ne_zero hn_ne_top, one_mul,
        div_eq_mul_inv, one_mul]
  have hd' : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (fun j => C j ∩ Set.Icc 0 (1 / (n : ℝ))) := by
    intro x _ y _ hxy
    refine Disjoint.mono (Set.inter_subset_left) (Set.inter_subset_left) ?_
    exact h_alloc.2.1 x y hxy
  have hm' : ∀ j, MeasurableSet (C j ∩ Set.Icc 0 (1 / (n : ℝ))) := by
    intro j
    exact (h_alloc.1 j).inter measurableSet_Icc
  have h_sum_f : ∑ j, MeasureTheory.volume (C j ∩ Set.Icc 0 (1 / (n : ℝ))) = MeasureTheory.volume (Set.Icc 0 (1 / (n : ℝ))) := by
    have h_biu := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) hd' (fun b _ => hm' b)
    rw [← h_biu]
    have h_union : (⋃ b ∈ (Finset.univ : Finset (Fin n)), C b ∩ Set.Icc 0 (1 / (n : ℝ))) = Set.Icc 0 (1 / (n : ℝ)) := by
      simp only [Finset.mem_univ, Set.iUnion_true]
      rw [← Set.iUnion_inter, h_alloc.2.2]
      apply Set.inter_eq_self_of_subset_right
      intro x hx
      rw [Set.mem_Icc] at hx ⊢
      refine ⟨hx.1, le_trans hx.2 ?_⟩
      have hn' : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      exact div_le_one_of_le₀ hn' (by linarith)
    rw [h_union]
  have h_vol_S : MeasureTheory.volume (Set.Icc (0 : ℝ) (1 / (n : ℝ))) = 1 / (n : ENNReal) := by
    rw [Real.volume_Icc, sub_zero]
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [ENNReal.ofReal_div_of_pos hn_pos]
    simp
  have h_sum_eq : ∑ j, MeasureTheory.volume (C j ∩ Set.Icc 0 (1 / (n : ℝ))) =
      ∑ _j : Fin n, (1 : ENNReal) / ((n : ENNReal) ^ 2) := by
    rw [h_sum_f, h_vol_S, h_sum_g]
  have h_top : (∑ _j : Fin n, (1 : ENNReal) / ((n : ENNReal) ^ 2)) ≠ ⊤ := by
    rw [h_sum_g]
    exact ENNReal.div_ne_top ENNReal.one_ne_top hn_ne_zero
  have h_res := h_eq_of_sum_eq i
    (fun j => MeasureTheory.volume (C j ∩ Set.Icc 0 (1 / (n : ℝ))))
    (fun _ => 1 / ((n : ENNReal) ^ 2))
    h_le h_sum_eq h_top
  rw [h_res]
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2_pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_pos
  rw [ENNReal.ofReal_div_of_pos hn2_pos]
  simp
