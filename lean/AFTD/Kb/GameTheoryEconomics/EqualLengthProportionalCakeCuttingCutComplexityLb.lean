import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCakeAllocation
import AFTD.Kb.GameTheoryEconomics.IsEqualLengthAllocation
import AFTD.Kb.GameTheoryEconomics.IsPropLbProportional
import AFTD.Kb.GameTheoryEconomics.CakeAllocationUsesAtMostCuts
import AFTD.Kb.GameTheoryEconomics.EqualLengthProportionalCakePrefixVolume
import AFTD.Kb.GameTheoryEconomics.EqualLengthProportionalCakeSuffixVolume
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# equal_length_proportional_cake_cutting_cut_complexity_lb

Topic: fair_division   Node: fc78a4ed1882

Provenance: formalization of a published result. Source: scout/2610-19733-exact-cut-complexity-of-equal-length-proportional-cake-cutt.md:374

For every integer n ≥ 1, if C : Fin n → Set ℝ is an equal-length proportional cake allocation among n agents under the identical valuation profile where each agent values only the prefix [0, 1/n], and C uses at most q cuts, then 2 * n - 2 ≤ q.
-/

open MeasureTheory Set

theorem equal_length_proportional_cake_cutting_cut_complexity_lb_castSucc_le_castSucc_of_lt {k : ℕ} {j1 j2 : Fin (k + 1)} (h : j1 < j2) :
    j1.succ ≤ j2.castSucc := by
  rw [Fin.le_def]
  have : (j1.succ : ℕ) = (j1 : ℕ) + 1 := rfl
  have : (j2.castSucc : ℕ) = (j2 : ℕ) := rfl
  omega

theorem equal_length_proportional_cake_cutting_cut_complexity_lb_pos_sub_sq (n : ℕ) (hn : 2 ≤ n) : 0 < 1 / (n : ℝ) - 1 / ((n : ℝ) ^ 2) := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have h1 : 1 / ((n : ℝ) ^ 2) < 1 / (n : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hn_pos]
    nlinarith
  linarith

theorem equal_length_proportional_cake_cutting_cut_complexity_lb_mem_piece_of_mem_Icc {k : ℕ} (t : Fin (k + 2) → ℝ)
    (_ht : StrictMono t) (ht0 : t 0 = 0) (ht1 : t (Fin.last (k + 1)) = 1)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : Fin (k + 1), x ∈ (if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) := by
  have hS_nonempty : ∃ j : Fin (k + 1), x ≤ t j.succ := by
    use Fin.last k
    rw [Fin.succ_last, ht1]
    exact hx.2
  let S : Finset (Fin (k + 1)) := Finset.filter (fun j => x ≤ t j.succ) Finset.univ
  have hS : S.Nonempty := by
    rcases hS_nonempty with ⟨j, hj⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  let j := Finset.min' S hS
  have hj_mem : x ≤ t j.succ := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  use j
  split_ifs with hj0
  · rw [hj0] at hj_mem ⊢
    rw [Fin.castSucc_zero, ht0]
    exact ⟨hx.1, hj_mem⟩
  · refine ⟨?_, hj_mem⟩
    let i : Fin k := j.pred hj0
    have hi_lt : i.castSucc < j := by
      rw [Fin.lt_def]
      have : (j : ℕ) = (i.succ : ℕ) := by rw [Fin.succ_pred]
      rw [this]
      exact Fin.castSucc_lt_succ
    have h_not : i.castSucc ∉ S := fun h => not_lt_of_ge (Finset.min'_le S _ h) hi_lt
    rw [Finset.mem_filter] at h_not
    have : ¬ (x ≤ t (i.castSucc).succ) := by
      intro h
      exact h_not ⟨Finset.mem_univ _, h⟩
    push Not at this
    have heq : (i.castSucc).succ = j.castSucc := by
      rw [Fin.succ_castSucc, Fin.succ_pred]
    rwa [heq] at this

theorem equal_length_proportional_cake_cutting_cut_complexity_lb_exists_piece_positive_measure {n k : ℕ} (C : Fin n → Set ℝ)
    (h_alloc : is_cake_allocation n C)
    (t : Fin (k + 2) → ℝ) (ht : StrictMono t) (ht0 : t 0 = 0) (ht1 : t (Fin.last (k + 1)) = 1)
    (c : Fin (k + 1) → Fin n)
    (hc : ∀ j, (if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ⊆ C (c j))
    (S : Set ℝ) (hS : S ⊆ Set.Icc 0 1)
    (i : Fin n) (hpos : 0 < MeasureTheory.volume (C i ∩ S)) :
    ∃ j : Fin (k + 1), c j = i ∧ 0 < MeasureTheory.volume ((if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ∩ S) := by
  let P : Fin (k + 1) → Set ℝ := fun j =>
    if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)
  have hsub : C i ∩ S ⊆ ⋃ j ∈ Finset.filter (fun j => c j = i) Finset.univ, (P j ∩ S) := by
    intro x hx
    have hxS : x ∈ S := hx.2
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := hS hxS
    obtain ⟨j, hj⟩ := equal_length_proportional_cake_cutting_cut_complexity_lb_mem_piece_of_mem_Icc t ht ht0 ht1 hxIcc
    have hjC : x ∈ C (c j) := hc j hj
    have hci : c j = i := by
      by_contra hneq
      have hdisj := h_alloc.2.1 (c j) i hneq
      exact (Set.disjoint_iff.mp hdisj) ⟨hjC, hx.1⟩
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hci, hj, hxS⟩
  by_contra h_none
  push Not at h_none
  have h_le := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub
  have h_biu : MeasureTheory.volume (⋃ j ∈ Finset.filter (fun j => c j = i) Finset.univ, (P j ∩ S)) ≤
      ∑ j ∈ Finset.filter (fun j => c j = i) Finset.univ, MeasureTheory.volume (P j ∩ S) :=
    measure_biUnion_finset_le _ _
  have h_sum_zero : ∑ j ∈ Finset.filter (fun j => c j = i) Finset.univ, MeasureTheory.volume (P j ∩ S) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact le_antisymm (h_none j hj) (bot_le)
  rw [h_sum_zero] at h_biu
  have : MeasureTheory.volume (C i ∩ S) ≤ 0 := le_trans h_le h_biu
  exact (ne_of_gt hpos) (le_antisymm this bot_le)

theorem equal_length_proportional_cake_cutting_cut_complexity_lb_castSucc_lt_of_pos_vol_Icc {k : ℕ} (t : Fin (k + 2) → ℝ)
    (j : Fin (k + 1)) (n : ℕ)
    (hvol : 0 < volume ((if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ∩ Set.Icc 0 (1 / (n : ℝ)))) :
    t j.castSucc < 1 / (n : ℝ) := by
  by_contra hle
  push Not at hle
  have hsub : ((if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ∩ Set.Icc 0 (1 / (n : ℝ))) ⊆ {1 / (n : ℝ)} := by
    intro x hx
    split_ifs at hx with hj0
    · simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_singleton_iff] at hx ⊢
      linarith
    · simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, Set.mem_singleton_iff] at hx ⊢
      linarith
  have h_le : volume ((if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ∩ Set.Icc 0 (1 / (n : ℝ))) ≤ volume ({1 / (n : ℝ)} : Set ℝ) :=
    measure_mono hsub
  rw [Real.volume_singleton] at h_le
  exact (ne_of_gt hvol) (le_antisymm h_le bot_le)

theorem equal_length_proportional_cake_cutting_cut_complexity_lb_lt_succ_of_pos_vol_Ioc {k : ℕ} (t : Fin (k + 2) → ℝ)
    (j : Fin (k + 1)) (n : ℕ)
    (hvol : 0 < volume ((if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ∩ Set.Ioc (1 / (n : ℝ)) 1)) :
    1 / (n : ℝ) < t j.succ := by
  by_contra hle
  push Not at hle
  have hsub : ((if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ∩ Set.Ioc (1 / (n : ℝ)) 1) ⊆ ∅ := by
    intro x hx
    split_ifs at hx with hj0
    · simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc] at hx
      linarith
    · simp only [Set.mem_inter_iff, Set.mem_Ioc] at hx
      linarith
  have h_le : volume ((if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)) ∩ Set.Ioc (1 / (n : ℝ)) 1) ≤ volume (∅ : Set ℝ) :=
    measure_mono hsub
  rw [measure_empty] at h_le
  exact (ne_of_gt hvol) (le_antisymm h_le bot_le)

/-- Proposition 1 (arXiv:2610.19733): Every equal-length proportional cake allocation under the lower-bound valuation profile requires at least 2n - 2 cuts. -/
theorem equal_length_proportional_cake_cutting_cut_complexity_lb (n : ℕ) (hn : 1 ≤ n)
    (C : Fin n → Set ℝ)
    (h_alloc : is_cake_allocation n C)
    (h_len : is_equal_length_allocation n C)
    (h_prop : is_prop_lb_proportional n C)
    (q : ℕ) (h_cuts : cake_allocation_uses_at_most_cuts n q C) :
    2 * n - 2 ≤ q := by
  by_cases hn2 : n < 2
  · have : n = 1 := by omega
    subst this
    omega
  have hn2' : 2 ≤ n := by omega
  rcases h_cuts with ⟨k, hkq, t, ht, ht0, ht1, hpieces⟩
  choose c hc using hpieces
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn_one_le : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hS1_sub : Set.Icc 0 (1 / (n : ℝ)) ⊆ Set.Icc 0 1 := by
    intro x hx
    refine ⟨hx.1, le_trans hx.2 ?_⟩
    exact div_le_one_of_le₀ hn_one_le (by linarith)
  have hS2_sub : Set.Ioc (1 / (n : ℝ)) 1 ⊆ Set.Icc 0 1 := by
    intro x hx
    refine ⟨le_trans (by positivity) (le_of_lt hx.1), hx.2⟩
  have h_prefix_pos : ∀ i : Fin n, 0 < volume (C i ∩ Set.Icc 0 (1 / (n : ℝ))) := by
    intro i
    rw [equal_length_proportional_cake_prefix_volume n hn C h_alloc h_len h_prop i]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have h_suffix_pos : ∀ i : Fin n, 0 < volume (C i ∩ Set.Ioc (1 / (n : ℝ)) 1) := by
    intro i
    rw [equal_length_proportional_cake_suffix_volume n hn C h_alloc h_len h_prop i]
    exact ENNReal.ofReal_pos.mpr (equal_length_proportional_cake_cutting_cut_complexity_lb_pos_sub_sq n hn2')
  let P : Fin (k + 1) → Set ℝ := fun j =>
    if j = 0 then Set.Icc (t j.castSucc) (t j.succ) else Set.Ioc (t j.castSucc) (t j.succ)
  let J1 : Finset (Fin (k + 1)) :=
    Finset.filter (fun j => 0 < volume (P j ∩ Set.Icc 0 (1 / (n : ℝ)))) Finset.univ
  let J2 : Finset (Fin (k + 1)) :=
    Finset.filter (fun j => 0 < volume (P j ∩ Set.Ioc (1 / (n : ℝ)) 1)) Finset.univ
  have hJ1_cov : ∀ i : Fin n, ∃ j ∈ J1, c j = i := by
    intro i
    obtain ⟨j, hjc, hjvol⟩ := equal_length_proportional_cake_cutting_cut_complexity_lb_exists_piece_positive_measure C h_alloc t ht ht0 ht1 c hc
      (Set.Icc 0 (1 / (n : ℝ))) hS1_sub i (h_prefix_pos i)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjvol⟩, hjc⟩
  have hJ2_cov : ∀ i : Fin n, ∃ j ∈ J2, c j = i := by
    intro i
    obtain ⟨j, hjc, hjvol⟩ := equal_length_proportional_cake_cutting_cut_complexity_lb_exists_piece_positive_measure C h_alloc t ht ht0 ht1 c hc
      (Set.Ioc (1 / (n : ℝ)) 1) hS2_sub i (h_suffix_pos i)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjvol⟩, hjc⟩
  have hn_le_J1 : n ≤ J1.card := by
    have : (Finset.univ : Finset (Fin n)) ⊆ J1.image c := by
      intro b _
      rcases hJ1_cov b with ⟨a, ha, rfl⟩
      exact Finset.mem_image_of_mem c ha
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_image_le (s := J1) (f := c)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact le_trans h1 h2
  have hn_le_J2 : n ≤ J2.card := by
    have : (Finset.univ : Finset (Fin n)) ⊆ J2.image c := by
      intro b _
      rcases hJ2_cov b with ⟨a, ha, rfl⟩
      exact Finset.mem_image_of_mem c ha
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_image_le (s := J2) (f := c)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact le_trans h1 h2
  have h_inter : (J1 ∩ J2).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro a b ha hb
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at ha hb
    have h_a_cast : t a.castSucc < 1 / (n : ℝ) :=
      equal_length_proportional_cake_cutting_cut_complexity_lb_castSucc_lt_of_pos_vol_Icc t a n ha.1.2
    have h_a_succ : 1 / (n : ℝ) < t a.succ :=
      equal_length_proportional_cake_cutting_cut_complexity_lb_lt_succ_of_pos_vol_Ioc t a n ha.2.2
    have h_b_cast : t b.castSucc < 1 / (n : ℝ) :=
      equal_length_proportional_cake_cutting_cut_complexity_lb_castSucc_lt_of_pos_vol_Icc t b n hb.1.2
    have h_b_succ : 1 / (n : ℝ) < t b.succ :=
      equal_length_proportional_cake_cutting_cut_complexity_lb_lt_succ_of_pos_vol_Ioc t b n hb.2.2
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have hle : a.succ ≤ b.castSucc :=
        equal_length_proportional_cake_cutting_cut_complexity_lb_castSucc_le_castSucc_of_lt hlt
      have ht_le : t a.succ ≤ t b.castSucc := ht.monotone hle
      linarith
    · exact heq
    · have hle : b.succ ≤ a.castSucc :=
        equal_length_proportional_cake_cutting_cut_complexity_lb_castSucc_le_castSucc_of_lt hgt
      have ht_le : t b.succ ≤ t a.castSucc := ht.monotone hle
      linarith
  have h_union_sub : J1 ∪ J2 ⊆ Finset.univ := Finset.subset_univ _
  have h_union_card : (J1 ∪ J2).card ≤ k + 1 := by
    have := Finset.card_le_card h_union_sub
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have h_sum := Finset.card_union_add_card_inter J1 J2
  omega
