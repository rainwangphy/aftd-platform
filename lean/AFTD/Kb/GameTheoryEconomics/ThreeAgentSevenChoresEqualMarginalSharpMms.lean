import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ThreeAgentCriticalEqualWeightAllocationFamily
import AFTD.Kb.GameTheoryEconomics.EqualWeightAllocationFamilyLottery
import AFTD.Kb.GameTheoryEconomics.IsScaledBivaluedChores
import AFTD.Kb.GameTheoryEconomics.IsEqualMarginalLottery
import AFTD.Kb.GameTheoryEconomics.IsExPostAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.Tcs.G

/-!
# three_agent_seven_chores_equal_marginal_sharp_mms

Topic: fair_division   Node: 1ebf96affeae

Provenance: original. Related work: OP-1112; extends the first critical case using high-count cost bounds, tested in experiments 26821 and 26831.

For three agents, seven chores, any ratio r in [1,2], and any scaled bivalued additive cost profile with common ratio r, there is a nonnegative weight for every complete allocation, with all weights summing to 1, such that each chore is assigned to each agent with marginal probability 1/3 and every allocation with positive weight gives each agent at most (r+1)/2 times her three-agent chore maximin share.
-/

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_cost_eq (r a : ℝ) (u : Fin 7 → ℝ)
    (hu : ∀ g, u g = a ∨ u g = r * a) (S : Finset (Fin 7)) :
    additive_valuation u S = (S.card : ℝ) * a + ((S.filter fun g => u g = r * a).card : ℝ) * ((r - 1) * a) := by
  have hpt : ∀ g, u g = a + (if u g = r * a then (r - 1) * a else 0) := by
    intro g
    by_cases h2 : u g = r * a
    · rw [if_pos h2, h2]; ring
    · rw [if_neg h2]
      rcases hu g with h | h
      · rw [h]; ring
      · exact absurd h h2
  show (∑ g ∈ S, u g) = _
  calc (∑ g ∈ S, u g) = ∑ g ∈ S, (a + (if u g = r * a then (r - 1) * a else 0)) :=
        Finset.sum_congr rfl (fun g _ => hpt g)
    _ = (∑ g ∈ S, a) + ∑ g ∈ S, (if u g = r * a then (r - 1) * a else 0) := Finset.sum_add_distrib
    _ = (S.card : ℝ) * a + ((S.filter fun g => u g = r * a).card : ℝ) * ((r - 1) * a) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_sum_bundle_card (P : Fin 7 → Fin 3) :
    ∑ k : Fin 3, (bundle_of P k).card = 7 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin 7)))
    (t := (Finset.univ : Finset (Fin 3))) (f := P) (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  simpa [bundle_of] using h.symm

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_exists_bundle_card_three
    (P : Fin 7 → Fin 3) : ∃ k : Fin 3, 3 ≤ (bundle_of P k).card := by
  have hsum := three_agent_seven_chores_equal_marginal_sharp_mms_sum_bundle_card P
  by_contra h
  simp only [not_exists, not_le] at h
  have h6 : ∀ k : Fin 3, (bundle_of P k).card ≤ 2 := fun k => by have := h k; omega
  have hle : ∑ k : Fin 3, (bundle_of P k).card ≤ 6 := by
    have h2 : ∑ k : Fin 3, (bundle_of P k).card ≤ ∑ _k : Fin 3, 2 :=
      Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => h6 k)
    simpa using h2
  omega

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_sum_high_card (P : Fin 7 → Fin 3)
    (HH : Finset (Fin 7)) : ∑ k : Fin 3, ((bundle_of P k) ∩ HH).card = HH.card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := HH)
    (t := (Finset.univ : Finset (Fin 3))) (f := P) (fun x _ => Finset.mem_univ _)
  have hterm : ∀ k : Fin 3, ((bundle_of P k) ∩ HH).card = (HH.filter fun x => P x = k).card := by
    intro k
    congr 1
    ext x
    simp only [bundle_of, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
  simpa using h.symm

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_filter_card_inter
    (u : Fin 7 → ℝ) (a r : ℝ) (S : Finset (Fin 7)) :
    (S.filter fun g => u g = r * a).card = (S ∩ (Finset.univ.filter fun g => u g = r * a)).card := by
  congr 1
  ext x
  simp [Finset.mem_filter, and_comm]

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_comb_five (s h : Fin 3 → ℕ)
    (hsum_s : ∑ k, s k = 7) (hsum_h : ∑ k, h k = 5) (hle : ∀ k, h k ≤ s k) :
    ∃ k, 4 ≤ s k ∨ (s k = 3 ∧ 1 ≤ h k) := by
  rw [Fin.sum_univ_three] at hsum_s hsum_h
  by_contra hcon
  simp only [not_exists, not_or, not_le, not_and] at hcon
  have c0 := hcon 0; have c1 := hcon 1; have c2 := hcon 2
  have b0 := hle 0; have b1 := hle 1; have b2 := hle 2
  have z0 : s 0 = 3 → h 0 = 0 := fun h' => by have := c0.2 h'; omega
  have z1 : s 1 = 3 → h 1 = 0 := fun h' => by have := c1.2 h'; omega
  have z2 : s 2 = 3 → h 2 = 0 := fun h' => by have := c2.2 h'; omega
  have y0 : h 0 ≤ 2 := by
    by_cases hh : s 0 = 3
    · have := z0 hh; omega
    · have := c0.1; omega
  have y1 : h 1 ≤ 2 := by
    by_cases hh : s 1 = 3
    · have := z1 hh; omega
    · have := c1.1; omega
  have y2 : h 2 ≤ 2 := by
    by_cases hh : s 2 = 3
    · have := z2 hh; omega
    · have := c2.1; omega
  have hex3 : s 0 = 3 ∨ s 1 = 3 ∨ s 2 = 3 := by
    have := c0.1; have := c1.1; have := c2.1; omega
  rcases hex3 with hh | hh | hh
  · have := z0 hh; omega
  · have := z1 hh; omega
  · have := z2 hh; omega

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_comb_six (s h : Fin 3 → ℕ)
    (hsum_s : ∑ k, s k = 7) (hsum_h : 6 ≤ ∑ k, h k) (hle : ∀ k, h k ≤ s k)
    (k : Fin 3) (hk : 3 ≤ s k) : 2 ≤ h k := by
  have hsplit_h : ∑ j : Fin 3, h j = h k + ∑ j ∈ (Finset.univ.erase k), h j := by
    rw [Finset.add_sum_erase _ (fun j => h j) (Finset.mem_univ k)]
  have hsplit_s : ∑ j : Fin 3, s j = s k + ∑ j ∈ (Finset.univ.erase k), s j := by
    rw [Finset.add_sum_erase _ (fun j => s j) (Finset.mem_univ k)]
  have hle' : ∑ j ∈ (Finset.univ.erase k), h j ≤ ∑ j ∈ (Finset.univ.erase k), s j :=
    Finset.sum_le_sum (fun j _ => hle j)
  omega

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_mms_ge_three (a r : ℝ) (ha : 0 < a)
    (hr1 : 1 ≤ r) (u : Fin 7 → ℝ) (hu : ∀ g, u g = a ∨ u g = r * a) :
    (3:ℝ)*a ≤ chore_maximin_share 3 u := by
  have hge : ∀ g, a ≤ u g := by
    intro g
    rcases hu g with h | h
    · rw [h]
    · rw [h]; nlinarith
  rw [chore_maximin_share]
  refine le_ciInf (fun P => ?_)
  obtain ⟨k, hk⟩ := three_agent_seven_chores_equal_marginal_sharp_mms_exists_bundle_card_three P
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove k)
  show (3:ℝ) * a ≤ ∑ g ∈ bundle_of P k, u g
  have h1 : ∑ g ∈ bundle_of P k, a ≤ ∑ g ∈ bundle_of P k, u g :=
    Finset.sum_le_sum (fun g _ => hge g)
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h3 : (3:ℝ) ≤ ((bundle_of P k).card : ℝ) := by exact_mod_cast hk
  have h2 : (3:ℝ) * a ≤ ((bundle_of P k).card : ℝ) * a := by nlinarith
  linarith

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_mms_ge_high_five (a r : ℝ) (ha : 0 < a)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (u : Fin 7 → ℝ) (hu : ∀ g, u g = a ∨ u g = r * a)
    (hHc : (Finset.univ.filter fun g => u g = r * a).card = 5) :
    (r + 2) * a ≤ chore_maximin_share 3 u := by
  have hra : (0:ℝ) ≤ (r - 1) * a := by nlinarith
  rw [chore_maximin_share]
  refine le_ciInf (fun P => ?_)
  have hsum_s : ∑ k : Fin 3, (bundle_of P k).card = 7 :=
    three_agent_seven_chores_equal_marginal_sharp_mms_sum_bundle_card P
  have hsum_h : ∑ k : Fin 3, ((bundle_of P k).filter fun g => u g = r * a).card = 5 := by
    rw [← hHc]
    rw [← three_agent_seven_chores_equal_marginal_sharp_mms_sum_high_card P
      (Finset.univ.filter fun g => u g = r * a)]
    exact Finset.sum_congr rfl
      (fun k _ => three_agent_seven_chores_equal_marginal_sharp_mms_filter_card_inter u a r (bundle_of P k))
  have hle : ∀ k : Fin 3, ((bundle_of P k).filter fun g => u g = r * a).card ≤ (bundle_of P k).card :=
    fun k => Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨k, hk⟩ := three_agent_seven_chores_equal_marginal_sharp_mms_comb_five _ _ hsum_s hsum_h hle
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove k)
  have hcost := three_agent_seven_chores_equal_marginal_sharp_mms_cost_eq r a u hu (bundle_of P k)
  rcases hk with hk | ⟨hk3, hk1⟩
  · have h1 : (4:ℝ) ≤ ((bundle_of P k).card : ℝ) := by exact_mod_cast hk
    have h2 : (0:ℝ) ≤ (((bundle_of P k).filter fun g => u g = r * a).card : ℝ) * ((r-1)*a) := by
      have h3 : (0:ℝ) ≤ (((bundle_of P k).filter fun g => u g = r * a).card : ℝ) := by positivity
      exact mul_nonneg h3 hra
    nlinarith
  · have h1 : (3:ℝ) ≤ ((bundle_of P k).card : ℝ) := by rw [hk3]; norm_num
    have h2 : (1:ℝ) ≤ (((bundle_of P k).filter fun g => u g = r * a).card : ℝ) := by exact_mod_cast hk1
    nlinarith

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_mms_ge_high_six (a r : ℝ) (ha : 0 < a)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (u : Fin 7 → ℝ) (hu : ∀ g, u g = a ∨ u g = r * a)
    (hHc : 6 ≤ (Finset.univ.filter fun g => u g = r * a).card) :
    (2*r + 1) * a ≤ chore_maximin_share 3 u := by
  have hra : (0:ℝ) ≤ (r - 1) * a := by nlinarith
  rw [chore_maximin_share]
  refine le_ciInf (fun P => ?_)
  have hsum_s : ∑ k : Fin 3, (bundle_of P k).card = 7 :=
    three_agent_seven_chores_equal_marginal_sharp_mms_sum_bundle_card P
  have hsum_h : 6 ≤ ∑ k : Fin 3, ((bundle_of P k).filter fun g => u g = r * a).card := by
    have heq : ∑ k : Fin 3, ((bundle_of P k).filter fun g => u g = r * a).card
        = (Finset.univ.filter fun g => u g = r * a).card := by
      rw [← three_agent_seven_chores_equal_marginal_sharp_mms_sum_high_card P
        (Finset.univ.filter fun g => u g = r * a)]
      exact Finset.sum_congr rfl
        (fun k _ => three_agent_seven_chores_equal_marginal_sharp_mms_filter_card_inter u a r (bundle_of P k))
    rw [heq]; exact hHc
  have hle : ∀ k : Fin 3, ((bundle_of P k).filter fun g => u g = r * a).card ≤ (bundle_of P k).card :=
    fun k => Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨k, hk3⟩ := three_agent_seven_chores_equal_marginal_sharp_mms_exists_bundle_card_three P
  have hk2 : 2 ≤ ((bundle_of P k).filter fun g => u g = r * a).card :=
    three_agent_seven_chores_equal_marginal_sharp_mms_comb_six _ _ hsum_s hsum_h hle k hk3
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove k)
  have hcost := three_agent_seven_chores_equal_marginal_sharp_mms_cost_eq r a u hu (bundle_of P k)
  have h1 : (3:ℝ) ≤ ((bundle_of P k).card : ℝ) := by exact_mod_cast hk3
  have h2 : (2:ℝ) ≤ (((bundle_of P k).filter fun g => u g = r * a).card : ℝ) := by exact_mod_cast hk2
  nlinarith

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_cost_le_of_mms (a r : ℝ) (ha : 0 < a)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (u : Fin 7 → ℝ) (hu : ∀ g, u g = a ∨ u g = r * a)
    (D : Finset (Fin 7)) (hD : D.card = 3) (m : ℕ)
    (hm : (D ∩ (Finset.univ.filter fun g => u g = r * a)).card ≤ m)
    (hmm : ((3:ℝ) + (m:ℝ) * (r - 1)) * a ≤ ((r + 1) / 2) * chore_maximin_share 3 u) :
    additive_valuation u D ≤ ((r + 1) / 2) * chore_maximin_share 3 u := by
  have hcost := three_agent_seven_chores_equal_marginal_sharp_mms_cost_eq r a u hu D
  have hda : (0:ℝ) ≤ (r-1)*a := by nlinarith
  have hsub : (D.filter fun g => u g = r * a).card ≤ m := by
    rw [three_agent_seven_chores_equal_marginal_sharp_mms_filter_card_inter]; exact hm
  have hmm' : ((D.filter fun g => u g = r * a).card : ℝ) ≤ (m:ℝ) := by exact_mod_cast hsub
  have h1 : additive_valuation u D ≤ ((D.card:ℝ) * a) + ((m:ℝ) * ((r-1)*a)) := by
    rw [hcost]
    have := mul_le_mul_of_nonneg_right hmm' hda
    linarith
  have hd3 : (D.card : ℝ) = 3 := by rw [hD]; norm_num
  have h2 : (D.card:ℝ) * a + (m:ℝ) * ((r-1)*a) ≤ ((r+1)/2) * chore_maximin_share 3 u := by
    have h3 : (D.card:ℝ) * a + (m:ℝ) * ((r-1)*a) = ((3:ℝ) + (m:ℝ)*(r-1))*a := by
      rw [hd3]; ring
    rw [h3]; exact hmm
  linarith

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_pair_bound (a r : ℝ) (ha : 0 < a)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (u : Fin 7 → ℝ) (hu : ∀ g, u g = a ∨ u g = r * a)
    (S : Finset (Fin 7)) (hS : S.card ≤ 2) :
    additive_valuation u S ≤ ((r + 1) / 2) * chore_maximin_share 3 u := by
  have hcost := three_agent_seven_chores_equal_marginal_sharp_mms_cost_eq r a u hu S
  have hle : (S.filter fun g => u g = r * a).card ≤ S.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hleR : ((S.filter fun g => u g = r * a).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hle
  have hda : (0:ℝ) ≤ (r-1)*a := by nlinarith
  have h1 : additive_valuation u S ≤ (S.card:ℝ)*a + (S.card:ℝ)*((r-1)*a) := by
    rw [hcost]
    have := mul_le_mul_of_nonneg_right hleR hda
    linarith
  have hSR : (S.card:ℝ) ≤ 2 := by exact_mod_cast hS
  have h2 : (S.card:ℝ)*a + (S.card:ℝ)*((r-1)*a) ≤ 2*r*a := by nlinarith
  have hmms := three_agent_seven_chores_equal_marginal_sharp_mms_mms_ge_three a r ha hr1 u hu
  have hr' : (0:ℝ) ≤ (r+1)/2 := by linarith
  have h3 : 2*r*a ≤ ((r+1)/2) * (3*a) := by nlinarith
  have h4 : ((r+1)/2) * (3*a) ≤ ((r+1)/2) * chore_maximin_share 3 u :=
    mul_le_mul_of_nonneg_left hmms hr'
  linarith

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_exists_designated (a r : ℝ)
    (u : Fin 7 → ℝ) :
    ∃ H : Finset (Fin 7), H.card = 4 ∧
      ((Finset.univ.filter fun g => u g = r * a) ⊆ H ∨
       H ⊆ Finset.univ.filter fun g => u g = r * a) := by
  by_cases hcase : (Finset.univ.filter fun g => u g = r * a).card ≤ 4
  · obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ.filter fun g => u g = r * a)ᶜ)
      (n := 4 - (Finset.univ.filter fun g => u g = r * a).card) (by
        rw [Finset.card_compl, Fintype.card_fin]; omega)
    refine ⟨Finset.univ.filter (fun g => u g = r * a) ∪ t, ?_, Or.inl Finset.subset_union_left⟩
    rw [Finset.card_union_of_disjoint (Finset.disjoint_left.2 ?_)]
    · omega
    · intro x hx hxt
      exact (Finset.mem_compl.mp (ht hxt)) hx
  · have h4 : 4 ≤ (Finset.univ.filter fun g => u g = r * a).card := by omega
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq
      (s := Finset.univ.filter fun g => u g = r * a) (n := 4) h4
    exact ⟨t, htc, Or.inr ht⟩

private lemma three_agent_seven_chores_equal_marginal_sharp_mms_triple_bound (a r : ℝ) (ha : 0 < a)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (u : Fin 7 → ℝ) (hu : ∀ g, u g = a ∨ u g = r * a)
    (H D : Finset (Fin 7)) (hH : H.card = 4)
    (hsub : (Finset.univ.filter fun g => u g = r * a) ⊆ H ∨
            H ⊆ Finset.univ.filter fun g => u g = r * a)
    (hD : D.card = 3) (hDH : (D ∩ H).card ≤ 1) :
    additive_valuation u D ≤ ((r + 1) / 2) * chore_maximin_share 3 u := by
  set HH : Finset (Fin 7) := Finset.univ.filter (fun g => u g = r * a) with hHH
  have hr' : (0:ℝ) ≤ (r+1)/2 := by linarith
  have hmms3 := three_agent_seven_chores_equal_marginal_sharp_mms_mms_ge_three a r ha hr1 u hu
  have key1 : (D ∩ HH).card ≤ 1 →
      additive_valuation u D ≤ ((r + 1) / 2) * chore_maximin_share 3 u := by
    intro hm
    have hm' : (D ∩ (Finset.univ.filter fun g => u g = r * a)).card ≤ 1 := by rwa [← hHH]
    apply three_agent_seven_chores_equal_marginal_sharp_mms_cost_le_of_mms a r ha hr1 hr2 u hu D hD 1 hm'
    have h1 := mul_le_mul_of_nonneg_left hmms3 hr'
    nlinarith
  have key2 : HH.card = 5 → (D ∩ HH).card ≤ 2 →
      additive_valuation u D ≤ ((r + 1) / 2) * chore_maximin_share 3 u := by
    intro hc5 hm
    have hc5' : (Finset.univ.filter fun g => u g = r * a).card = 5 := by rwa [← hHH]
    have hm' : (D ∩ (Finset.univ.filter fun g => u g = r * a)).card ≤ 2 := by rwa [← hHH]
    have hmms := three_agent_seven_chores_equal_marginal_sharp_mms_mms_ge_high_five a r ha hr1 hr2 u hu hc5'
    apply three_agent_seven_chores_equal_marginal_sharp_mms_cost_le_of_mms a r ha hr1 hr2 u hu D hD 2 hm'
    have h1 := mul_le_mul_of_nonneg_left hmms hr'
    nlinarith
  rcases hsub with hsub | hsub
  · have hle : (D ∩ HH).card ≤ 1 := by
      have h2 : D ∩ HH ⊆ D ∩ H := by
        intro x hx
        exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hsub (Finset.mem_inter.1 hx).2⟩
      exact le_trans (Finset.card_le_card h2) hDH
    exact key1 hle
  · have h4 : 4 ≤ HH.card := by
      rw [← hH]; exact Finset.card_le_card hsub
    have hmsub : (D ∩ HH).card ≤ 1 + (HH.card - 4) := by
      have hsub2 : D ∩ HH ⊆ (D ∩ H) ∪ (HH \ H) := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
        by_cases hxH : x ∈ H
        · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hx1, hxH⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hx2, hxH⟩)
      have h1 := Finset.card_le_card hsub2
      have h2 := Finset.card_union_le (D ∩ H) (HH \ H)
      have h3 : (HH \ H).card = HH.card - 4 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, hH]
      omega
    have hc45 : HH.card = 4 ∨ HH.card = 5 ∨ 6 ≤ HH.card := by omega
    rcases hc45 with hc | hc | hc
    · have hle : (D ∩ HH).card ≤ 1 := by rw [hc] at hmsub; simpa using hmsub
      exact key1 hle
    · have hle : (D ∩ HH).card ≤ 2 := by rw [hc] at hmsub; simpa using hmsub
      exact key2 hc hle
    · have hc6' : 6 ≤ (Finset.univ.filter fun g => u g = r * a).card := by rwa [← hHH]
      have hm' : (D ∩ (Finset.univ.filter fun g => u g = r * a)).card ≤ 3 := by
        rw [← hHH]
        have := Finset.card_le_card (Finset.inter_subset_left : D ∩ HH ⊆ D)
        omega
      have hmms :=
        three_agent_seven_chores_equal_marginal_sharp_mms_mms_ge_high_six a r ha hr1 hr2 u hu hc6'
      apply three_agent_seven_chores_equal_marginal_sharp_mms_cost_le_of_mms a r ha hr1 hr2 u hu D hD 3 hm'
      have h1 := mul_le_mul_of_nonneg_left hmms hr'
      nlinarith

theorem three_agent_seven_chores_equal_marginal_sharp_mms (r : ℝ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (c : Fin 3 → Fin 7 → ℝ) (hc : is_scaled_bivalued_chores r c) : ∃ p ∈ stdSimplex ℝ (Fin 7 → Fin 3), is_equal_marginal_lottery p ∧ is_ex_post_alpha_mms_chores ((r+1)/2) c p := by
  classical
  obtain ⟨a, ha, hca⟩ := hc
  choose H hH hHsub using fun i =>
    three_agent_seven_chores_equal_marginal_sharp_mms_exists_designated (a i) r (c i)
  obtain ⟨F, hbij, hcard, hdiag⟩ := three_agent_critical_equal_weight_allocation_family H hH
  refine equal_weight_allocation_family_lottery 3 7 (by norm_num) ((r+1)/2) c F hbij ?_
  intro t i
  by_cases hit : i = t
  · rw [hit]
    exact three_agent_seven_chores_equal_marginal_sharp_mms_triple_bound (a t) r (ha t) hr1 hr2 (c t)
      (hca t) (H t) (bundle_of (F t) t) (hH t) (hHsub t) (by simpa using hcard t t) (hdiag t)
  · refine three_agent_seven_chores_equal_marginal_sharp_mms_pair_bound (a i) r (ha i) hr1 hr2 (c i)
      (hca i) (bundle_of (F t) i) ?_
    rw [hcard t i, if_neg hit]
