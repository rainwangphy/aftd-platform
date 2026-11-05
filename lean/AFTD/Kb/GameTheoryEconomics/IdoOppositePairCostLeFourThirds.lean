import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsIdenticallyOrdered
import AFTD.Kb.GameTheoryEconomics.ChoreOppositePair
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ido_opposite_pair_cost_le_four_thirds

Topic: fair_division   Node: 20d105a8cbdb

Provenance: helper lemma. arXiv:2611.04884 Lemma 4.1

In an identically ordered instance of m chores and n agents with 2 * n ≤ m and nonnegative costs c where every agent has maximin share 1, for every agent i : Fin n and index j : Fin n, the additive valuation of chore_opposite_pair h2n j under c i is at most 4/3.
-/

/-- In an IDO instance with MMS 1, each opposite pair has additive cost at most 4/3. -/
lemma ido_opposite_pair_cost_le_four_thirds
    (n m : ℕ) (h2n : 2 * n ≤ m) (c : Fin n → Fin m → ℝ)
    (hc_nonneg : ∀ i e, 0 ≤ c i e)
    (h_ido : is_identically_ordered c)
    (h_mms : ∀ i : Fin n, chore_maximin_share n (c i) = 1)
    (i : Fin n) (j : Fin n) :
    additive_valuation (c i) (chore_opposite_pair h2n j) ≤ 4 / 3 := by
  have hj : (j : ℕ) < n := j.isLt
  let e1 : Fin m := ⟨j.val, by omega⟩
  let e2 : Fin m := ⟨2 * n - 1 - j.val, by omega⟩
  have he12 : e1 ≤ e2 := by
    change e1.val ≤ e2.val
    dsimp [e1, e2]
    omega
  have h_pair_val : additive_valuation (c i) (chore_opposite_pair h2n j) = c i e1 + c i e2 := by
    unfold additive_valuation chore_opposite_pair
    dsimp only
    have hne : (⟨j.val, by omega⟩ : Fin m) ≠ ⟨2 * n - 1 - j.val, by omega⟩ := by
      intro h
      have h' : j.val = 2 * n - 1 - j.val := Fin.ext_iff.mp h
      omega
    rw [Finset.sum_pair hne]
  have h_e1_le_one : c i e1 ≤ 1 := by
    have hP : ∀ P : Fin m → Fin n, c i e1 ≤ ⨆ k, additive_valuation (c i) (bundle_of P k) := by
      intro P
      have he_in : e1 ∈ bundle_of P (P e1) := Finset.mem_filter.mpr ⟨Finset.mem_univ e1, rfl⟩
      have he_le : c i e1 ≤ additive_valuation (c i) (bundle_of P (P e1)) := by
        dsimp [additive_valuation]
        have : c i e1 = ∑ x ∈ {e1}, c i x := by simp
        rw [this]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_singleton] at hx
          rw [hx]
          exact he_in
        · intro x _ _
          exact hc_nonneg i x
      have h_le_sup : additive_valuation (c i) (bundle_of P (P e1)) ≤ ⨆ k', additive_valuation (c i) (bundle_of P k') :=
        le_ciSup (Finite.bddAbove_range (fun k' => additive_valuation (c i) (bundle_of P k'))) (P e1)
      linarith
    have h_mms_i := h_mms i
    dsimp [chore_maximin_share] at h_mms_i
    have : Nonempty (Fin m → Fin n) := ⟨fun _ => i⟩
    have h_le_inf : c i e1 ≤ ⨅ P, ⨆ k, additive_valuation (c i) (bundle_of P k) :=
      le_ciInf hP
    rw [h_mms_i] at h_le_inf
    exact h_le_inf
  have hT_card : (Finset.Iic e2).card = 2 * n - j.val := by
    rw [Fin.card_Iic e2]
    dsimp [e2]
    omega
  have hT0_card : (Finset.Iic e1).card = j.val + 1 := by
    rw [Fin.card_Iic e1]
  have hT0_sub_T : Finset.Iic e1 ⊆ Finset.Iic e2 := Finset.Iic_subset_Iic.mpr he12
  have hP_bound : ∀ P : Fin m → Fin n, min (3 * c i e2) (c i e1 + c i e2) ≤ ⨆ k, additive_valuation (c i) (bundle_of P k) := by
    intro P
    let S (k : Fin n) : Finset (Fin m) := (Finset.Iic e2).filter (fun x => P x = k)
    let S0 (k : Fin n) : Finset (Fin m) := (Finset.Iic e1).filter (fun x => P x = k)
    have hS_sub : ∀ k, S0 k ⊆ S k := by
      intro k x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hT0_sub_T hx.1, hx.2⟩
    have hS_sum : ∑ k : Fin n, (S k).card = 2 * n - j.val := by
      rw [← hT_card]
      exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (P x))).symm
    have hS0_sum : ∑ k : Fin n, (S0 k).card = j.val + 1 := by
      rw [← hT0_card]
      exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (P x))).symm
    by_cases h_ge3 : ∃ k : Fin n, 3 ≤ (S k).card
    · obtain ⟨k, hk⟩ := h_ge3
      have hSy_sub : S k ⊆ bundle_of P k := by
        intro x hx
        rw [Finset.mem_filter] at hx
        simp only [Finset.mem_filter, bundle_of, Finset.mem_univ, true_and]
        exact hx.2
      have hSy_le_bundle : ∑ x ∈ S k, c i x ≤ ∑ x ∈ bundle_of P k, c i x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hSy_sub
        intro x _ _
        exact hc_nonneg i x
      have h_cg_le_x : ∀ x ∈ S k, c i e2 ≤ c i x := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have hxb : x ≤ e2 := Finset.mem_Iic.mp hx.1
        exact h_ido i hxb
      have h_sum_cg : ((S k).card : ℝ) * c i e2 ≤ ∑ x ∈ S k, c i x := by
        have : ∑ _x ∈ S k, c i e2 ≤ ∑ x ∈ S k, c i x := Finset.sum_le_sum h_cg_le_x
        simpa using this
      have h3_card : 3 * c i e2 ≤ ((S k).card : ℝ) * c i e2 := by
        have hcie2 : 0 ≤ c i e2 := hc_nonneg i e2
        have h3_le : (3 : ℝ) ≤ ((S k).card : ℝ) := by
          exact_mod_cast hk
        nlinarith
      have h3_bundle : 3 * c i e2 ≤ additive_valuation (c i) (bundle_of P k) := by
        dsimp [additive_valuation]
        linarith
      have h_le_sup : additive_valuation (c i) (bundle_of P k) ≤ ⨆ k', additive_valuation (c i) (bundle_of P k') :=
        le_ciSup (Finite.bddAbove_range (fun k' => additive_valuation (c i) (bundle_of P k'))) k
      have : min (3 * c i e2) (c i e1 + c i e2) ≤ 3 * c i e2 := min_le_left _ _
      linarith
    · have h_le2 : ∀ k : Fin n, (S k).card ≤ 2 := by
        intro k
        by_contra h_gt
        apply h_ge3
        exact ⟨k, by omega⟩
      have hex : ∃ k : Fin n, 1 ≤ (S0 k).card ∧ 2 ≤ (S k).card := by
        by_contra h_none
        have h_sum_le : ∀ k : Fin n, (S k).card + (S0 k).card ≤ 2 := by
          intro k
          have := h_le2 k
          have := Finset.card_le_card (hS_sub k)
          have hk_not : ¬(1 ≤ (S0 k).card ∧ 2 ≤ (S k).card) := fun h => h_none ⟨k, h⟩
          omega
        have h_total : ∑ k : Fin n, ((S k).card + (S0 k).card) ≤ ∑ k : Fin n, 2 := by
          apply Finset.sum_le_sum
          intro k _
          exact h_sum_le k
        rw [Finset.sum_add_distrib, hS_sum, hS0_sum] at h_total
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_total
        omega
      obtain ⟨k0, hk0_1, hk0_2⟩ := hex
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (S0 k0).card)
      have ha_in_S : a ∈ S k0 := hS_sub k0 ha
      have hS_erase_card : 1 ≤ ((S k0).erase a).card := by
        rw [Finset.card_erase_of_mem ha_in_S]
        omega
      obtain ⟨b, hb_mem⟩ := Finset.card_pos.mp (by omega : 0 < ((S k0).erase a).card)
      have hb_in_S : b ∈ S k0 := Finset.mem_of_mem_erase hb_mem
      have hba : b ≠ a := Finset.ne_of_mem_erase hb_mem
      have hab : a ≠ b := hba.symm
      have ha_le_e1 : a ≤ e1 := by
        have := (Finset.mem_filter.mp ha).1
        exact Finset.mem_Iic.mp this
      have hb_le_e2 : b ≤ e2 := by
        have := (Finset.mem_filter.mp hb_in_S).1
        exact Finset.mem_Iic.mp this
      have h_pair_sub : {a, b} ⊆ bundle_of P k0 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · have := (Finset.mem_filter.mp ha_in_S).2
          simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
          exact this
        · have := (Finset.mem_filter.mp hb_in_S).2
          simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
          exact this
      have h_sum_le : c i a + c i b ≤ additive_valuation (c i) (bundle_of P k0) := by
        dsimp [additive_valuation]
        have h_pair_sum : c i a + c i b = ∑ x ∈ {a, b}, c i x := by
          rw [Finset.sum_pair hab]
        rw [h_pair_sum]
        apply Finset.sum_le_sum_of_subset_of_nonneg h_pair_sub
        intro x _ _
        exact hc_nonneg i x
      have h_cia : c i e1 ≤ c i a := h_ido i ha_le_e1
      have h_cib : c i e2 ≤ c i b := h_ido i hb_le_e2
      have h_bundle_le : c i e1 + c i e2 ≤ additive_valuation (c i) (bundle_of P k0) := by
        linarith
      have h_le_sup : additive_valuation (c i) (bundle_of P k0) ≤ ⨆ k', additive_valuation (c i) (bundle_of P k') :=
        le_ciSup (Finite.bddAbove_range (fun k' => additive_valuation (c i) (bundle_of P k'))) k0
      have : min (3 * c i e2) (c i e1 + c i e2) ≤ c i e1 + c i e2 := min_le_right _ _
      linarith
  have h_mms_i := h_mms i
  dsimp [chore_maximin_share] at h_mms_i
  have : Nonempty (Fin m → Fin n) := ⟨fun _ => i⟩
  have h_le_inf : min (3 * c i e2) (c i e1 + c i e2) ≤ ⨅ P, ⨆ k, additive_valuation (c i) (bundle_of P k) :=
    le_ciInf hP_bound
  rw [h_mms_i] at h_le_inf
  have h_cases : 3 * c i e2 ≤ 1 ∨ c i e1 + c i e2 ≤ 1 := by
    exact min_le_iff.mp h_le_inf
  have h_sum_le_four_thirds : c i e1 + c i e2 ≤ 4 / 3 := by
    rcases h_cases with h1 | h2
    · have : c i e2 ≤ 1 / 3 := by linarith
      linarith
    · linarith
  rw [h_pair_val]
  exact h_sum_le_four_thirds
