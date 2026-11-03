import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BivaluedTwoAgentEfxFamilyFeasible
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts

Topic: fair_division   Node: 40df17778b12

Provenance: helper lemma. arXiv:2610.14994 (Section 4.2, Theorem 4.1: two agents, scaled common-ratio bivalued goods admit an EFX, fPO and envy-freeable allocation)

Normalized two-agent bivalued core from the EFX arithmetic: if both agents' values lie in {1, r} and for every choice of the four type multiplicities the EFX arithmetic predicate bivalued_two_agent_efx_family_feasible holds, then there is an allocation that is EFX, has nonnegative aggregate a0*(v0(A0)-v0(A1)) + a1*(v1(A1)-v1(A0)) >= 0, and admits a positive weight tie t > 0 (u0(g) <= t*u1(g) on agent 1's goods, t*u1(g) <= u0(g) on agent 0's goods).
-/

private lemma scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
    {m : ℕ} (u : Fin m → ℝ) (c : ℝ) (T : Finset (Fin m))
    (h : ∀ g ∈ T, u g = c) : additive_valuation u T = T.card * c := by
  simp only [additive_valuation, Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

private lemma scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_union
    {m : ℕ} (u : Fin m → ℝ) (S T : Finset (Fin m))
    (h : Disjoint S T) : additive_valuation u (S ∪ T) = additive_valuation u S + additive_valuation u T := by
  simp only [additive_valuation]
  exact Finset.sum_union h

private lemma scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_erase
    {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) (g : Fin m)
    (hg : g ∈ S) : additive_valuation u (S.erase g) = additive_valuation u S - u g := by
  simp only [additive_valuation]
  have h := Finset.sum_erase_add S u hg
  linarith

private lemma scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_four
    {m : ℕ} (u : Fin m → ℝ) (A B C D : Finset (Fin m))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) :
    additive_valuation u (A ∪ B ∪ C ∪ D) =
      additive_valuation u A + additive_valuation u B + additive_valuation u C + additive_valuation u D := by
  have h1 : Disjoint (A ∪ B ∪ C) D := by
    rw [Finset.disjoint_left] at *
    intro x hx hD
    simp only [Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    · exact hAD hx hD
    · exact hBD hx hD
    · exact hCD hx hD
  have h2 : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left] at *
    intro x hx hC
    simp only [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hAC hx hC
    · exact hBC hx hC
  rw [scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_union
        (u := u) (S := A ∪ B ∪ C) (T := D) h1,
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_union
        (u := u) (S := A ∪ B) (T := C) h2,
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_union
        (u := u) (S := A) (T := B) hAB]

theorem scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts
    (m : ℕ) (r : ℝ) (hr : 1 < r) (a0 a1 : ℝ) (h0 : 0 < a0) (hpos : 0 < a1)
    (u : Fin 2 → Fin m → ℝ) (hu : ∀ i g, u i g = 1 ∨ u i g = r)
    (harith : ∀ n1 n2 n3 n4 : ℕ, bivalued_two_agent_efx_family_feasible n1 n2 n3 n4 r a0 a1) :
    ∃ σ : Fin m → Fin 2, is_efx_goods u σ ∧
      (0 ≤ a0 * (additive_valuation (u 0) (bundle_of σ 0) - additive_valuation (u 0) (bundle_of σ 1))
         + a1 * (additive_valuation (u 1) (bundle_of σ 1) - additive_valuation (u 1) (bundle_of σ 0))) ∧
      ∃ t : ℝ, 0 < t ∧ ∀ g : Fin m,
        (σ g = 1 → u 0 g ≤ t * u 1 g) ∧ (σ g = 0 → t * u 1 g ≤ u 0 g) := by
  classical
  set C1 : Finset (Fin m) := Finset.univ.filter (fun g => u 0 g = 1 ∧ u 1 g = 1) with hC1
  set C2 : Finset (Fin m) := Finset.univ.filter (fun g => u 0 g = 1 ∧ u 1 g = r) with hC2
  set C3 : Finset (Fin m) := Finset.univ.filter (fun g => u 0 g = r ∧ u 1 g = 1) with hC3
  set C4 : Finset (Fin m) := Finset.univ.filter (fun g => u 0 g = r ∧ u 1 g = r) with hC4
  have hm1 : ∀ g : Fin m, g ∈ C1 ↔ (u 0 g = 1 ∧ u 1 g = 1) := fun g => by simp [hC1]
  have hm2 : ∀ g : Fin m, g ∈ C2 ↔ (u 0 g = 1 ∧ u 1 g = r) := fun g => by simp [hC2]
  have hm3 : ∀ g : Fin m, g ∈ C3 ↔ (u 0 g = r ∧ u 1 g = 1) := fun g => by simp [hC3]
  have hm4 : ∀ g : Fin m, g ∈ C4 ↔ (u 0 g = r ∧ u 1 g = r) := fun g => by simp [hC4]
  have hne : (1:ℝ) ≠ r := ne_of_lt hr
  have hd12 : Disjoint C1 C2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hm1] at hx1; rw [hm2] at hx2
    exact hne (hx1.2.symm.trans hx2.2)
  have hd13 : Disjoint C1 C3 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx3
    rw [hm1] at hx1; rw [hm3] at hx3
    exact hne (hx1.1.symm.trans hx3.1)
  have hd14 : Disjoint C1 C4 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx4
    rw [hm1] at hx1; rw [hm4] at hx4
    exact hne (hx1.1.symm.trans hx4.1)
  have hd23 : Disjoint C2 C3 := by
    rw [Finset.disjoint_left]
    intro x hx2 hx3
    rw [hm2] at hx2; rw [hm3] at hx3
    exact hne (hx2.1.symm.trans hx3.1)
  have hd24 : Disjoint C2 C4 := by
    rw [Finset.disjoint_left]
    intro x hx2 hx4
    rw [hm2] at hx2; rw [hm4] at hx4
    exact hne (hx2.1.symm.trans hx4.1)
  have hd34 : Disjoint C3 C4 := by
    rw [Finset.disjoint_left]
    intro x hx3 hx4
    rw [hm3] at hx3; rw [hm4] at hx4
    exact hne (hx3.2.symm.trans hx4.2)
  have hcover : ∀ g : Fin m, g ∈ C1 ∨ g ∈ C2 ∨ g ∈ C3 ∨ g ∈ C4 := by
    intro g
    rcases hu 0 g with h0' | h0' <;> rcases hu 1 g with h1' | h1'
    · exact Or.inl ((hm1 g).2 ⟨h0', h1'⟩)
    · exact Or.inr (Or.inl ((hm2 g).2 ⟨h0', h1'⟩))
    · exact Or.inr (Or.inr (Or.inl ((hm3 g).2 ⟨h0', h1'⟩)))
    · exact Or.inr (Or.inr (Or.inr ((hm4 g).2 ⟨h0', h1'⟩)))
  have hunion : C1 ∪ C2 ∪ C3 ∪ C4 = Finset.univ := by
    ext g
    constructor
    · intro _; exact Finset.mem_univ g
    · intro _; simpa using hcover g
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hfam, hEFX0, hEFX1, hagg⟩ :=
    harith C1.card C2.card C3.card C4.card
  set L0 : ℝ := (if C1.card - a + (C2.card - b) ≥ 1 then (1:ℝ) else if C3.card - c + (C4.card - d) ≥ 1 then r else 0) with hL0
  set L1 : ℝ := (if a + c ≥ 1 then (1:ℝ) else if b + d ≥ 1 then r else 0) with hL1
  obtain ⟨T1, hT1s, hT1c⟩ := Finset.exists_subset_card_eq (s := C1) (n := a) ha
  obtain ⟨T2, hT2s, hT2c⟩ := Finset.exists_subset_card_eq (s := C2) (n := b) hb
  obtain ⟨T3, hT3s, hT3c⟩ := Finset.exists_subset_card_eq (s := C3) (n := c) hc
  obtain ⟨T4, hT4s, hT4c⟩ := Finset.exists_subset_card_eq (s := C4) (n := d) hd
  set B0 : Finset (Fin m) := T1 ∪ T2 ∪ T3 ∪ T4 with hB0
  have hbun0 : bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 0 = B0 := by
    ext g; simp [bundle_of]
  have hbun1 : bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 1 = Finset.univ \ B0 := by
    ext g; simp [bundle_of]
  have hdT12 : Disjoint T1 T2 := hd12.mono hT1s hT2s
  have hdT13 : Disjoint T1 T3 := hd13.mono hT1s hT3s
  have hdT14 : Disjoint T1 T4 := hd14.mono hT1s hT4s
  have hdT23 : Disjoint T2 T3 := hd23.mono hT2s hT3s
  have hdT24 : Disjoint T2 T4 := hd24.mono hT2s hT4s
  have hdT34 : Disjoint T3 T4 := hd34.mono hT3s hT4s
  have hv0B0 : additive_valuation (u 0) B0 = ↑a + ↑b + r * ↑c + r * ↑d := by
    rw [hB0, scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_four
          (u := u 0) (A := T1) (B := T2) (C := T3) (D := T4)
          hdT12 hdT13 hdT14 hdT23 hdT24 hdT34,
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) 1 T1 (fun g hg => ((hm1 g).1 (hT1s hg)).1),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) 1 T2 (fun g hg => ((hm2 g).1 (hT2s hg)).1),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) r T3 (fun g hg => ((hm3 g).1 (hT3s hg)).1),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) r T4 (fun g hg => ((hm4 g).1 (hT4s hg)).1),
      hT1c, hT2c, hT3c, hT4c]
    ring
  have hv1B0 : additive_valuation (u 1) B0 = ↑a + r * ↑b + ↑c + r * ↑d := by
    rw [hB0, scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_four
          (u := u 1) (A := T1) (B := T2) (C := T3) (D := T4)
          hdT12 hdT13 hdT14 hdT23 hdT24 hdT34,
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) 1 T1 (fun g hg => ((hm1 g).1 (hT1s hg)).2),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) r T2 (fun g hg => ((hm2 g).1 (hT2s hg)).2),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) 1 T3 (fun g hg => ((hm3 g).1 (hT3s hg)).2),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) r T4 (fun g hg => ((hm4 g).1 (hT4s hg)).2),
      hT1c, hT2c, hT3c, hT4c]
    ring
  have hv0univ : additive_valuation (u 0) Finset.univ = ↑C1.card + ↑C2.card + r * ↑C3.card + r * ↑C4.card := by
    rw [← hunion, scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_four
          (u := u 0) (A := C1) (B := C2) (C := C3) (D := C4)
          hd12 hd13 hd14 hd23 hd24 hd34,
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) 1 C1 (fun g hg => ((hm1 g).1 hg).1),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) 1 C2 (fun g hg => ((hm2 g).1 hg).1),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) r C3 (fun g hg => ((hm3 g).1 hg).1),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 0) r C4 (fun g hg => ((hm4 g).1 hg).1)]
    ring
  have hv1univ : additive_valuation (u 1) Finset.univ = ↑C1.card + r * ↑C2.card + ↑C3.card + r * ↑C4.card := by
    rw [← hunion, scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_four
          (u := u 1) (A := C1) (B := C2) (C := C3) (D := C4)
          hd12 hd13 hd14 hd23 hd24 hd34,
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) 1 C1 (fun g hg => ((hm1 g).1 hg).2),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) r C2 (fun g hg => ((hm2 g).1 hg).2),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) 1 C3 (fun g hg => ((hm3 g).1 hg).2),
      scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_const
        (u 1) r C4 (fun g hg => ((hm4 g).1 hg).2)]
    ring
  have hsplit0 : additive_valuation (u 0) B0 + additive_valuation (u 0) (Finset.univ \ B0)
      = additive_valuation (u 0) Finset.univ := by
    rw [← scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_union
          (u 0) B0 (Finset.univ \ B0) Finset.disjoint_sdiff, Finset.union_sdiff_of_subset]
    intro x hx; exact Finset.mem_univ x
  have hsplit1 : additive_valuation (u 1) B0 + additive_valuation (u 1) (Finset.univ \ B0)
      = additive_valuation (u 1) Finset.univ := by
    rw [← scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_union
          (u 1) B0 (Finset.univ \ B0) Finset.disjoint_sdiff, Finset.union_sdiff_of_subset]
    intro x hx; exact Finset.mem_univ x
  have hU1 : additive_valuation (u 0) (Finset.univ \ B0)
      = ↑(C1.card - a) + ↑(C2.card - b) + r * ↑(C3.card - c) + r * ↑(C4.card - d) := by
    have e1 : ((C1.card - a : ℕ) : ℝ) = (C1.card : ℝ) - (a : ℝ) := by rw [Nat.cast_sub ha]
    have e2 : ((C2.card - b : ℕ) : ℝ) = (C2.card : ℝ) - (b : ℝ) := by rw [Nat.cast_sub hb]
    have e3 : ((C3.card - c : ℕ) : ℝ) = (C3.card : ℝ) - (c : ℝ) := by rw [Nat.cast_sub hc]
    have e4 : ((C4.card - d : ℕ) : ℝ) = (C4.card : ℝ) - (d : ℝ) := by rw [Nat.cast_sub hd]
    rw [e1, e2, e3, e4]
    ring_nf
    linarith [hsplit0, hv0B0, hv0univ]
  have hV1 : additive_valuation (u 1) (Finset.univ \ B0)
      = ↑(C1.card - a) + r * ↑(C2.card - b) + ↑(C3.card - c) + r * ↑(C4.card - d) := by
    have e1 : ((C1.card - a : ℕ) : ℝ) = (C1.card : ℝ) - (a : ℝ) := by rw [Nat.cast_sub ha]
    have e2 : ((C2.card - b : ℕ) : ℝ) = (C2.card : ℝ) - (b : ℝ) := by rw [Nat.cast_sub hb]
    have e3 : ((C3.card - c : ℕ) : ℝ) = (C3.card : ℝ) - (c : ℝ) := by rw [Nat.cast_sub hc]
    have e4 : ((C4.card - d : ℕ) : ℝ) = (C4.card : ℝ) - (d : ℝ) := by rw [Nat.cast_sub hd]
    rw [e1, e2, e3, e4]
    ring_nf
    linarith [hsplit1, hv1B0, hv1univ]
  have hu0ge1 : ∀ g : Fin m, 1 ≤ u 0 g := fun g => by rcases hu 0 g with h | h <;> linarith
  have hu1ge1 : ∀ g : Fin m, 1 ≤ u 1 g := fun g => by rcases hu 1 g with h | h <;> linarith
  have hmemB0 : ∀ g : Fin m, g ∈ B0 ↔ (g ∈ T1 ∨ g ∈ T2 ∨ g ∈ T3 ∨ g ∈ T4) := by
    intro g; rw [hB0]; simp
  have hT1full : a = C1.card → T1 = C1 := fun h => by
    refine Finset.eq_of_subset_of_card_le hT1s ?_
    rw [hT1c, h]
  have hT2full : b = C2.card → T2 = C2 := fun h => by
    refine Finset.eq_of_subset_of_card_le hT2s ?_
    rw [hT2c, h]
  have hT3full : c = C3.card → T3 = C3 := fun h => by
    refine Finset.eq_of_subset_of_card_le hT3s ?_
    rw [hT3c, h]
  have hT4full : d = C4.card → T4 = C4 := fun h => by
    refine Finset.eq_of_subset_of_card_le hT4s ?_
    rw [hT4c, h]
  have hL0le : ∀ g ∈ bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 1, L0 ≤ u 0 g := by
    intro g hg
    have hgB : g ∉ B0 := by
      rw [hbun1] at hg
      simpa using hg
    rw [hL0]
    split_ifs with hA hB
    · linarith [hu0ge1 g]
    · have ha' : a = C1.card := by omega
      have hb' : b = C2.card := by omega
      have hT1e : T1 = C1 := hT1full ha'
      have hT2e : T2 = C2 := hT2full hb'
      have hnot1 : g ∉ C1 := by
        rw [← hT1e]
        intro h'
        exact hgB ((hmemB0 g).2 (Or.inl h'))
      have hnot2 : g ∉ C2 := by
        rw [← hT2e]
        intro h'
        exact hgB ((hmemB0 g).2 (Or.inr (Or.inl h')))
      rcases hcover g with h | h | h | h
      · exact absurd h hnot1
      · exact absurd h hnot2
      · rw [((hm3 g).1 h).1]
      · rw [((hm4 g).1 h).1]
    · linarith [hu0ge1 g]
  have hL1le : ∀ g ∈ bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 0, L1 ≤ u 1 g := by
    intro g hg
    have hgB : g ∈ B0 := by rw [hbun0] at hg; exact hg
    rw [hL1]
    split_ifs with hA hB
    · linarith [hu1ge1 g]
    · have ha0 : a = 0 := by omega
      have hc0 : c = 0 := by omega
      have hT1e : T1 = ∅ := Finset.card_eq_zero.1 (by rw [hT1c, ha0])
      have hT3e : T3 = ∅ := Finset.card_eq_zero.1 (by rw [hT3c, hc0])
      rcases (hmemB0 g).1 hgB with h | h | h | h
      · rw [hT1e] at h; exact absurd h (Finset.notMem_empty g)
      · rw [((hm2 g).1 (hT2s h)).2]
      · rw [hT3e] at h; exact absurd h (Finset.notMem_empty g)
      · rw [((hm4 g).1 (hT4s h)).2]
    · linarith [hu1ge1 g]
  have hfin : ∀ i : Fin 2, i = 0 ∨ i = 1 := fun i => by
    have h2 : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
    rcases h2 with h | h
    · exact Or.inl (Fin.ext (by simpa using h))
    · exact Or.inr (Fin.ext (by simpa using h))
  have hefx : is_efx_goods u (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) := by
    intro i j hij g hg
    have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
      rcases hfin i with h | h <;> rcases hfin j with h' | h'
      · exact absurd (h.trans h'.symm) hij
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
      · exact absurd (h.trans h'.symm) hij
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h3 : additive_valuation (u 0) (bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 1)
          ≤ additive_valuation (u 0) (bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 0) + L0 := by
        rw [hbun0, hbun1, hU1, hv0B0]
        exact hEFX0
      have h1 := scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_erase
        (u 0) (bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 1) g hg
      have h2 := hL0le g hg
      linarith
    · have h3 : additive_valuation (u 1) (bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 0)
          ≤ additive_valuation (u 1) (bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 1) + L1 := by
        rw [hbun0, hbun1, hV1, hv1B0]
        exact hEFX1
      have h1 := scaled_common_ratio_bivalued_efx_fpo_envyfreeable_two_agents_core_of_efx_counts_addval_erase
        (u 1) (bundle_of (fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1) 0) g hg
      have h2 := hL1le g hg
      linarith
  refine ⟨fun g : Fin m => if g ∈ B0 then (0:Fin 2) else 1, hefx, ?_, ?_⟩
  · rw [hbun0, hbun1, hv0B0, hU1, hv1B0, hV1]
    exact hagg
  · rcases hfam with ⟨hb0, hc3⟩ | ⟨ha0, hb0, hd0⟩ | ⟨ha1, hc3, hd4⟩
    · have hT2e : T2 = ∅ := Finset.card_eq_zero.1 (by rw [hT2c, hb0])
      have hT3e : T3 = C3 := hT3full hc3
      refine ⟨1, one_pos, ?_⟩
      intro g
      have hsig1 : (if g ∈ B0 then (0:Fin 2) else 1) = 1 ↔ g ∉ B0 := by by_cases h : g ∈ B0 <;> simp [h]
      have hsig0 : (if g ∈ B0 then (0:Fin 2) else 1) = 0 ↔ g ∈ B0 := by by_cases h : g ∈ B0 <;> simp [h]
      constructor
      · intro hg
        have hgB : g ∉ B0 := hsig1.1 hg
        rw [one_mul]
        rcases hcover g with h | h | h | h
        · have h1 := (hm1 g).1 h; rw [h1.1, h1.2]
        · have h2 := (hm2 g).1 h; rw [h2.1, h2.2]; linarith
        · exact absurd (hT3e ▸ h) (fun hT3 => hgB ((hmemB0 g).2 (Or.inr (Or.inr (Or.inl hT3)))))
        · have h4 := (hm4 g).1 h; rw [h4.1, h4.2]
      · intro hg
        have hgB : g ∈ B0 := hsig0.1 hg
        rw [one_mul]
        rcases (hmemB0 g).1 hgB with h | h | h | h
        · have h1 := (hm1 g).1 (hT1s h); rw [h1.2, h1.1]
        · rw [hT2e] at h; exact absurd h (Finset.notMem_empty g)
        · have h3 := (hm3 g).1 (hT3e ▸ h); rw [h3.2, h3.1]; linarith
        · have h4 := (hm4 g).1 (hT4s h); rw [h4.2, h4.1]
    · have hT1e : T1 = ∅ := Finset.card_eq_zero.1 (by rw [hT1c, ha0])
      have hT2e : T2 = ∅ := Finset.card_eq_zero.1 (by rw [hT2c, hb0])
      have hT4e : T4 = ∅ := Finset.card_eq_zero.1 (by rw [hT4c, hd0])
      refine ⟨r, by linarith, ?_⟩
      intro g
      have hsig1 : (if g ∈ B0 then (0:Fin 2) else 1) = 1 ↔ g ∉ B0 := by by_cases h : g ∈ B0 <;> simp [h]
      have hsig0 : (if g ∈ B0 then (0:Fin 2) else 1) = 0 ↔ g ∈ B0 := by by_cases h : g ∈ B0 <;> simp [h]
      constructor
      · intro hg
        have hgB : g ∉ B0 := hsig1.1 hg
        rcases hcover g with h | h | h | h
        · have h1 := (hm1 g).1 h; rw [h1.1, h1.2]; linarith
        · have h2 := (hm2 g).1 h; rw [h2.1, h2.2]; nlinarith
        · have h3 := (hm3 g).1 h; rw [h3.1, h3.2]; linarith
        · have h4 := (hm4 g).1 h; rw [h4.1, h4.2]; nlinarith
      · intro hg
        have hgB : g ∈ B0 := hsig0.1 hg
        rcases (hmemB0 g).1 hgB with h | h | h | h
        · rw [hT1e] at h; exact absurd h (Finset.notMem_empty g)
        · rw [hT2e] at h; exact absurd h (Finset.notMem_empty g)
        · have h3 := (hm3 g).1 (hT3s h); rw [h3.1, h3.2]; linarith
        · rw [hT4e] at h; exact absurd h (Finset.notMem_empty g)
    · have hT1e : T1 = C1 := hT1full ha1
      have hT3e : T3 = C3 := hT3full hc3
      have hT4e : T4 = C4 := hT4full hd4
      have h1r : (1:ℝ)/r * r = 1 := by field_simp
      have h1rle : (1:ℝ)/r ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      refine ⟨1/r, by positivity, ?_⟩
      intro g
      have hsig1 : (if g ∈ B0 then (0:Fin 2) else 1) = 1 ↔ g ∉ B0 := by by_cases h : g ∈ B0 <;> simp [h]
      have hsig0 : (if g ∈ B0 then (0:Fin 2) else 1) = 0 ↔ g ∈ B0 := by by_cases h : g ∈ B0 <;> simp [h]
      constructor
      · intro hg
        have hgB : g ∉ B0 := hsig1.1 hg
        have hnot1 : g ∉ C1 := fun h => hgB ((hmemB0 g).2 (Or.inl (hT1e ▸ h)))
        have hnot3 : g ∉ C3 := fun h => hgB ((hmemB0 g).2 (Or.inr (Or.inr (Or.inl (hT3e ▸ h)))))
        have hnot4 : g ∉ C4 := fun h => hgB ((hmemB0 g).2 (Or.inr (Or.inr (Or.inr (hT4e ▸ h)))))
        have hC2 : g ∈ C2 := by
          rcases hcover g with h | h | h | h
          · exact absurd h hnot1
          · exact h
          · exact absurd h hnot3
          · exact absurd h hnot4
        have h2 := (hm2 g).1 hC2
        rw [h2.1, h2.2, h1r]
      · intro hg
        have hgB : g ∈ B0 := hsig0.1 hg
        rcases (hmemB0 g).1 hgB with h | h | h | h
        · have h1 := (hm1 g).1 (hT1s h); rw [h1.1, h1.2]; linarith
        · have h2 := (hm2 g).1 (hT2s h); rw [h2.1, h2.2, h1r]
        · have h3 := (hm3 g).1 (hT3e ▸ h); rw [h3.1, h3.2]; linarith
        · have h4 := (hm4 g).1 (hT4s h); rw [h4.1, h4.2, h1r]; linarith
